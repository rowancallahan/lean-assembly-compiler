# LEANSVG_TARGETS.md

Derived from `origin/leansvg-depth` (`LEANSVG_DEPTH.md`, `Testing/leansvg/depth/{res,g,rs}.json`, `ana.py`). No compiler code touched; no new frontx runs. Generator: `Testing/leansvg/targets/targets.py` (reruns `ana.py`'s classifier on the committed data).

**Terms.** *S(f)* = set of first-failure classes over f and its user-defined callee closure (what the probe can see). *Only X* = S(f) = {X} and no callee in the closure lacks a verdict (`NOOUT`). *⚠ possibly unblocked* = blocked only by var×var `*` or `/`,`%` by a variable, which NOTES §22 (main, `Testing/notes/frontx/NOTES.md:1373`) says now compile for `Nat`/`UInt*` (not `Int`; inference, see §5).

## 0. Counts

- user-level functions probed: 2256 (probe reported 2 247 user defs; the extra 9 are generated/instance entries kept by the name filter); compile (`OK`): 43; first-failure `FAIL`: 2015; no verdict `NOOUT`: 198.
- functions whose closure has a `NOOUT` callee (so *only X* is not established): 475.

| feature class | FAIL with this first failure | *only X* rows (§1) |
|---|---|---|
| structure ctor / field projection / instance (user structure values) | 282 | 266 |
| user structure / inductive as parameter or result | 491 | 328 |
| Int / Fx scalar (also Int tuples, Option Int) | 383 | 279 |
| Array (of scalars, tuples or structures) as value | 328 | 160 |
| recursion shape | 47 | 47 |
| step proof fails (front-end limit; e.g. u8/shift facts) | 77 | 35 |
| Option of structure / tuple | 88 | 35 |
| String / Std.Format / Char | 39 | 26 |
| body shape not a scalar (do-block / join point) | 29 | 14 |
| function-typed value (closure) | 4 | 3 |
| match shape (multi-scrutinee, Bool-pair, literal patterns, Decidable.rec) | 34 | 13 |
| variable x variable `*` (Nat), nonlinear bound | 29 | 15 |

## 1. Functions blocked only by one feature (smallest first)

Columns: function, `file:line` (module from the probe, file name inferred), ≈lines (gap to the next declaration in the same module; includes blank/comment lines, so an upper bound; `?` = last in module), the first-failure message (truncated).

The first failure hides everything after it in the same body, so a row is *only X as far as the probe can see*; the body may need further features once X is fixed (§5).

### 1.1 structure ctor / field projection / instance (user structure values)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `BasicShape.Env.mk` | BasicShape.lean:81 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.Env.mk |  |
| 2 | `BasicShape.Geo.circle` | BasicShape.lean:62 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.Geo.circle |  |
| 3 | `BasicShape.Geo.ellipse` | BasicShape.lean:63 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.Geo.ellipse |  |
| 4 | `BasicShape.Geo.polygon` | BasicShape.lean:68 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.Geo.polygon |  |
| 5 | `BasicShape.LP.mk` | BasicShape.lean:41 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.LP.mk |  |
| 6 | `BasicShape.Spec.mk` | BasicShape.lean:74 | 1 | frontx: no unfolding equation for LeanSvg.BasicShape.Spec.mk |  |
| 7 | `Box.mk` | Geom.lean:332 | 1 | frontx: no unfolding equation for LeanSvg.Box.mk |  |
| 8 | `Brotli.Blocks.mk` | Brotli.lean:241 | 1 | frontx: no unfolding equation for LeanSvg.Brotli.Blocks.mk |  |
| 9 | `Brotli.Code.mk` | Brotli.lean:62 | 1 | frontx: no unfolding equation for LeanSvg.Brotli.Code.mk |  |
| 10 | `Canvas.mk` | Canvas.lean:23 | 1 | frontx: no unfolding equation for LeanSvg.Canvas.mk |  |
| 11 | `Clip.Mask.mk` | Clip.lean:86 | 1 | frontx: no unfolding equation for LeanSvg.Clip.Mask.mk |  |
| 12 | `Css.AttrOp.contains` | Css.lean:49 | 1 | frontx: no unfolding equation for LeanSvg.Css.AttrOp.contains |  |
| 13 | `Css.AttrOp.eq` | Css.lean:48 | 1 | frontx: no unfolding equation for LeanSvg.Css.AttrOp.eq |  |
| 14 | `Css.Compound.hasType` | Css.lean:54 | 1 | unknown free variable `_fvar.130` |  |
| 15 | `Css.Compound.id` | Css.lean:56 | 1 | unknown free variable `_fvar.299` |  |
| 16 | `Css.Compound.mk` | Css.lean:53 | 1 | frontx: no unfolding equation for LeanSvg.Css.Compound.mk |  |
| 17 | `Css.Compound.typeName` | Css.lean:55 | 1 | unknown free variable `_fvar.470` |  |
| 18 | `Css.Decl.mk` | Css.lean:86 | 1 | frontx: no unfolding equation for LeanSvg.Css.Decl.mk |  |
| 19 | `Css.Decl.name` | Css.lean:87 | 1 | unknown free variable `_fvar.670` |  |
| 20 | `Css.ElemInfo.id` | Css.lean:100 | 1 | unknown free variable `_fvar.859` |  |
| 21 | `Css.ElemInfo.mk` | Css.lean:98 | 1 | frontx: no unfolding equation for LeanSvg.Css.ElemInfo.mk |  |
| 22 | `Css.ElemInfo.tag` | Css.lean:99 | 1 | unknown free variable `_fvar.186` |  |
| 23 | `Css.Rule.mk` | Css.lean:92 | 1 | frontx: no unfolding equation for LeanSvg.Css.Rule.mk |  |
| 24 | `DSeg.mk` | Geom.lean:844 | 1 | frontx: no unfolding equation for LeanSvg.DSeg.mk |  |
| 25 | `FeImage.Href.elem` | Filter/Image.lean:42 | 1 | frontx: no unfolding equation for LeanSvg.FeImage.Href.elem |  |
| 26 | `FeImage.Job.mk` | Filter/ImageRender.lean:17 | 1 | frontx: no unfolding equation for LeanSvg.FeImage.Job.mk |  |
| 27 | `FeImage.Spec.mk` | Filter/Image.lean:48 | 1 | frontx: no unfolding equation for LeanSvg.FeImage.Spec.mk |  |
| 28 | `Filter.CMKind.matrix` | Filter.lean:168 | 1 | frontx: no unfolding equation for LeanSvg.Filter.CMKind.matrix |  |
| 29 | `Filter.CMKind.saturate` | Filter.lean:169 | 1 | frontx: no unfolding equation for LeanSvg.Filter.CMKind.saturate |  |
| 30 | `Filter.Kind.blend` | Filter.lean:199 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.blend |  |
| 31 | `Filter.Kind.blur` | Filter.lean:196 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.blur |  |
| 32 | `Filter.Kind.colorMatrix` | Filter.lean:201 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.colorMatrix |  |
| 33 | `Filter.Kind.composite` | Filter.lean:200 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.composite |  |
| 34 | `Filter.Kind.dropShadow` | Filter.lean:197 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.dropShadow |  |
| 35 | `Filter.Kind.flood` | Filter.lean:194 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.flood |  |
| 36 | `Filter.Kind.image` | Filter.lean:203 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.image |  |
| 37 | `Filter.Kind.lighting` | Filter.lean:210 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.lighting |  |
| 38 | `Filter.Kind.merge` | Filter.lean:198 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.merge |  |
| 39 | `Filter.Kind.morphology` | Filter.lean:205 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.morphology |  |
| 40 | `Filter.Kind.offset` | Filter.lean:195 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.offset |  |
| 41 | `Filter.Kind.tile` | Filter.lean:211 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.tile |  |
| 42 | `Filter.Kind.transfer` | Filter.lean:202 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.transfer |  |
| 43 | `Filter.Kind.turbulence` | Filter.lean:204 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Kind.turbulence |  |
| 44 | `Filter.Len.num` | Filter.lean:427 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Len.num |  |
| 45 | `Filter.Parsers.mk` | Filter.lean:303 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Parsers.mk |  |
| 46 | `Filter.RawFilter.id` | Filter.lean:289 | 1 | unknown free variable `_fvar.172` |  |
| 47 | `Filter.RawFilter.mk` | Filter.lean:288 | 1 | frontx: no unfolding equation for LeanSvg.Filter.RawFilter.mk |  |
| 48 | `Filter.RawPrim.linear` | Filter.lean:278 | 1 | unknown free variable `_fvar.572` |  |
| 49 | `Filter.RawPrim.mk` | Filter.lean:275 | 1 | frontx: no unfolding equation for LeanSvg.Filter.RawPrim.mk |  |
| 50 | `Filter.RawPrim.name` | Filter.lean:276 | 1 | unknown free variable `_fvar.743` |  |
| 51 | `Filter.Resolved.mk` | Filter.lean:247 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Resolved.mk |  |
| 52 | `Filter.TF.discrete` | Filter.lean:179 | 1 | frontx: no unfolding equation for LeanSvg.Filter.TF.discrete |  |
| 53 | `Filter.TF.linear` | Filter.lean:180 | 1 | frontx: no unfolding equation for LeanSvg.Filter.TF.linear |  |
| 54 | `Filter.TF.table` | Filter.lean:178 | 1 | frontx: no unfolding equation for LeanSvg.Filter.TF.table |  |
| 55 | `Filter.Table.mk` | Filter.lean:296 | 1 | frontx: no unfolding equation for LeanSvg.Filter.Table.mk |  |
| 56 | `Filter.URect.mk` | Filter.lean:227 | 1 | frontx: no unfolding equation for LeanSvg.Filter.URect.mk |  |
| 57 | `FilterApply.Img.mk` | FilterApply.lean:106 | 1 | frontx: no unfolding equation for LeanSvg.FilterApply.Img.mk |  |
| 58 | `FilterFrame.Back.mk` | FilterFrame.lean:35 | 1 | frontx: no unfolding equation for LeanSvg.FilterFrame.Back.mk |  |
| 59 | `FilterFrame.Plan.mk` | FilterFrame.lean:52 | 1 | frontx: no unfolding equation for LeanSvg.FilterFrame.Plan.mk |  |
| 60 | `Font.Tables.mk` | Font.lean:168 | 1 | frontx: no unfolding equation for LeanSvg.Font.Tables.mk |  |
| 61 | `Font.mk` | Font.lean:42 | 1 | frontx: no unfolding equation for LeanSvg.Font.mk |  |
| 62 | `FontFace.Face.mk` | FontFace.lean:46 | 1 | frontx: no unfolding equation for LeanSvg.FontFace.Face.mk |  |
| 63 | `FontSet.Entry.family` | FontSet.lean:81 | 1 | unknown free variable `_fvar.53679` |  |
| 64 | `FontSet.Entry.mk` | FontSet.lean:80 | 1 | frontx: no unfolding equation for LeanSvg.FontSet.Entry.mk |  |
| 65 | `ForeignObject.HStyle.mk` | ForeignObject.lean:63 | 1 | frontx: no unfolding equation for LeanSvg.ForeignObject.HStyle.mk |  |
| 66 | `ForeignObject.Item.text` | ForeignObject.lean:79 | 1 | frontx: no unfolding equation for LeanSvg.ForeignObject.Item.text |  |
| 67 | `ForeignObject.Line.mk` | ForeignObject.lean:252 | 1 | frontx: no unfolding equation for LeanSvg.ForeignObject.Line.mk |  |
| 68 | `Grad.Aff.mk` | Shader.lean:182 | 1 | frontx: no unfolding equation for LeanSvg.Grad.Aff.mk |  |
| 69 | `Grad.Axis.mk` | Shader.lean:656 | 1 | frontx: no unfolding equation for LeanSvg.Grad.Axis.mk |  |
| 70 | `Grad.Defs.mk` | Shader.lean:415 | 1 | frontx: no unfolding equation for LeanSvg.Grad.Defs.mk |  |
| 71 | `Grad.PctRef.mk` | Shader.lean:505 | 1 | frontx: no unfolding equation for LeanSvg.Grad.PctRef.mk |  |
| 72 | `Grad.RawDef.id` | Shader.lean:354 | 1 | unknown free variable `_fvar.508` |  |
| 73 | `Grad.RawDef.mk` | Shader.lean:353 | 1 | frontx: no unfolding equation for LeanSvg.Grad.RawDef.mk |  |
| 74 | `Grad.RawDef.oBB` | Shader.lean:358 | 1 | unknown free variable `_fvar.707` |  |
| 75 | `Grad.RawStop.mk` | Shader.lean:340 | 1 | frontx: no unfolding equation for LeanSvg.Grad.RawStop.mk |  |
| 76 | `Grad.Resolved.mk` | Shader.lean:405 | 1 | frontx: no unfolding equation for LeanSvg.Grad.Resolved.mk |  |
| 77 | `Grad.Rt.mk` | Shader.lean:678 | 1 | frontx: no unfolding equation for LeanSvg.Grad.Rt.mk |  |
| 78 | `Image.Pix.mk` | Image.lean:229 | 1 | frontx: no unfolding equation for LeanSvg.Image.Pix.mk |  |
| 79 | `Image.Placed.mk` | Image.lean:298 | 1 | frontx: no unfolding equation for LeanSvg.Image.Placed.mk |  |
| 80 | `Image.Rt.mk` | Image.lean:352 | 1 | frontx: no unfolding equation for LeanSvg.Image.Rt.mk |  |
| 81 | `ImageData.Decoded.mk` | ImageData.lean:19 | 1 | frontx: no unfolding equation for LeanSvg.ImageData.Decoded.mk |  |
| 82 | `Inflate.Huff.mk` | Inflate.lean:35 | 1 | frontx: no unfolding equation for LeanSvg.Inflate.Huff.mk |  |
| 83 | `JpegDecode.Comp.mk` | JpegDecode.lean:83 | 1 | frontx: no unfolding equation for LeanSvg.JpegDecode.Comp.mk |  |
| 84 | `JpegDecode.Frame.mk` | JpegDecode.lean:92 | 1 | frontx: no unfolding equation for LeanSvg.JpegDecode.Frame.mk |  |
| 85 | `Lighting.Light.distant` | Filter/Lighting.lean:36 | 1 | frontx: no unfolding equation for LeanSvg.Lighting.Light.distant |  |
| 86 | `Lighting.Light.point` | Filter/Lighting.lean:37 | 1 | frontx: no unfolding equation for LeanSvg.Lighting.Light.point |  |
| 87 | `Lighting.Params.mk` | Filter/Lighting.lean:43 | 1 | frontx: no unfolding equation for LeanSvg.Lighting.Params.mk |  |
| 88 | `Mask.Step.mk` | Mask.lean:39 | 1 | frontx: no unfolding equation for LeanSvg.Mask.Step.mk |  |
| 89 | `Mat.mk` | Geom.lean:61 | 1 | frontx: no unfolding equation for LeanSvg.Mat.mk |  |
| 90 | `Pat.Defs.mk` | Pattern.lean:127 | 1 | frontx: no unfolding equation for LeanSvg.Pat.Defs.mk |  |
| 91 | `Pat.RawDef.hasTransform` | Pattern.lean:75 | 1 | unknown free variable `_fvar.67` |  |
| 92 | `Pat.RawDef.id` | Pattern.lean:64 | 1 | unknown free variable `_fvar.574` |  |
| 93 | `Pat.RawDef.mk` | Pattern.lean:63 | 1 | frontx: no unfolding equation for LeanSvg.Pat.RawDef.mk |  |
| 94 | `Pat.Rt.mk` | PatternRender.lean:69 | 1 | frontx: no unfolding equation for LeanSvg.Pat.Rt.mk |  |
| 95 | `PathCmd.cubicTo` | Geom.lean:151 | 1 | frontx: no unfolding equation for LeanSvg.PathCmd.cubicTo |  |
| 96 | `PathCmd.lineTo` | Geom.lean:150 | 1 | frontx: no unfolding equation for LeanSvg.PathCmd.lineTo |  |
| 97 | `PathCmd.moveTo` | Geom.lean:149 | 1 | frontx: no unfolding equation for LeanSvg.PathCmd.moveTo |  |
| 98 | `PngDecode.Fmt.mk` | PngDecode.lean:177 | 1 | frontx: no unfolding equation for LeanSvg.PngDecode.Fmt.mk |  |
| 99 | `PngDecode.Hdr.mk` | PngDecode.lean:43 | 1 | frontx: no unfolding equation for LeanSvg.PngDecode.Hdr.mk |  |
| 100 | `PngDecode.Meta.mk` | PngDecode.lean:70 | 1 | frontx: no unfolding equation for LeanSvg.PngDecode.Meta.mk |  |
| 101 | `Poly.mk` | Geom.lean:157 | 1 | frontx: no unfolding equation for LeanSvg.Poly.mk |  |
| 102 | `Pt.mk` | Geom.lean:12 | 1 | frontx: no unfolding equation for LeanSvg.Pt.mk |  |
| 103 | `Raster.Mask.mk` | Raster.lean:65 | 1 | frontx: no unfolding equation for LeanSvg.Raster.Mask.mk |  |
| 104 | `Render.Clip.mk` | Render.lean:60 | 1 | frontx: no unfolding equation for LeanSvg.Render.Clip.mk |  |
| 105 | `Render.Layer.mk` | Render.lean:477 | 1 | frontx: no unfolding equation for LeanSvg.Render.Layer.mk |  |
| 106 | `Render.Target.mk` | Render.lean:219 | 1 | frontx: no unfolding equation for LeanSvg.Render.Target.mk |  |
| 107 | `Rgba.mk` | Canvas.lean:16 | 1 | frontx: no unfolding equation for LeanSvg.Rgba.mk |  |
| 108 | `Shape.Builder.mk` | Shape.lean:309 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Builder.mk |  |
| 109 | `Shape.FeatureInfo.mk` | Shape.lean:299 | 1 | frontx: no unfolding equation for LeanSvg.Shape.FeatureInfo.mk |  |
| 110 | `Shape.Indic.Cfg.mk` | ShapeRun.lean:711 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Indic.Cfg.mk |  |
| 111 | `Shape.Indic.Re.alt` | ShapeRun.lean:543 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Indic.Re.alt |  |
| 112 | `Shape.Indic.Re.seq` | ShapeRun.lean:542 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Indic.Re.seq |  |
| 113 | `Shape.Plan.mk` | Shape.lean:340 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Plan.mk |  |
| 114 | `Shape.Rule.mk` | Shape.lean:944 | 1 | frontx: no unfolding equation for LeanSvg.Shape.Rule.mk |  |
| 115 | `Shape.St.mk` | Shape.lean:474 | 1 | frontx: no unfolding equation for LeanSvg.Shape.St.mk |  |
| 116 | `ShapeText.SGlyph.mk` | ShapeText.lean:40 | 1 | frontx: no unfolding equation for LeanSvg.ShapeText.SGlyph.mk |  |
| 117 | `StrokeStyle.mk` | Geom.lean:486 | 1 | frontx: no unfolding equation for LeanSvg.StrokeStyle.mk |  |
| 118 | `Svg.ClipChild.mk` | Svg.lean:371 | 1 | frontx: no unfolding equation for LeanSvg.Svg.ClipChild.mk |  |
| 119 | `Svg.ClipEntry.mk` | Svg.lean:387 | 1 | frontx: no unfolding equation for LeanSvg.Svg.ClipEntry.mk |  |
| 120 | `Svg.ClipEntry.selfClip` | Svg.lean:400 | 1 | unknown free variable `_fvar.21234` |  |
| 121 | `Svg.ClipEntry.selfClipId` | Svg.lean:399 | 1 | unknown free variable `_fvar.21402` |  |
| 122 | `Svg.ClipMode.clip` | Svg.lean:3667 | 1 | frontx: no unfolding equation for LeanSvg.Svg.ClipMode.clip |  |
| 123 | `Svg.ClipUse.entry` | Svg.lean:422 | 1 | unknown free variable `_fvar.460` |  |
| 124 | `Svg.ClipUse.id` | Svg.lean:421 | 1 | unknown free variable `_fvar.630` |  |
| 125 | `Svg.ClipUse.mk` | Svg.lean:420 | 1 | frontx: no unfolding equation for LeanSvg.Svg.ClipUse.mk |  |
| 126 | `Svg.CtxUse.mk` | Svg.lean:410 | 1 | frontx: no unfolding equation for LeanSvg.Svg.CtxUse.mk |  |
| 127 | `Svg.DefsScan.mk` | Svg.lean:2860 | 1 | frontx: no unfolding equation for LeanSvg.Svg.DefsScan.mk |  |
| 128 | `Svg.Doc.mk` | Svg.lean:598 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Doc.mk |  |
| 129 | `Svg.Frame.mk` | Svg.lean:3700 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Frame.mk |  |
| 130 | `Svg.MarkerEntry.alignNone` | Svg.lean:560 | 1 | unknown free variable `_fvar.552` |  |
| 131 | `Svg.MarkerEntry.alignX` | Svg.lean:561 | 1 | unknown free variable `_fvar.577` |  |
| 132 | `Svg.MarkerEntry.alignY` | Svg.lean:562 | 1 | unknown free variable `_fvar.602` |  |
| 133 | `Svg.MarkerEntry.id` | Svg.lean:549 | 1 | unknown free variable `_fvar.1032` |  |
| 134 | `Svg.MarkerEntry.mk` | Svg.lean:548 | 1 | frontx: no unfolding equation for LeanSvg.Svg.MarkerEntry.mk |  |
| 135 | `Svg.MarkerEntry.slice` | Svg.lean:563 | 1 | unknown free variable `_fvar.30` |  |
| 136 | `Svg.MaskEntry.contentBBox` | Svg.lean:505 | 1 | unknown free variable `_fvar.373` |  |
| 137 | `Svg.MaskEntry.id` | Svg.lean:503 | 1 | unknown free variable `_fvar.732` |  |
| 138 | `Svg.MaskEntry.linear` | Svg.lean:508 | 1 | unknown free variable `_fvar.755` |  |
| 139 | `Svg.MaskEntry.mk` | Svg.lean:502 | 1 | frontx: no unfolding equation for LeanSvg.Svg.MaskEntry.mk |  |
| 140 | `Svg.MaskEntry.selfMask` | Svg.lean:517 | 1 | unknown free variable `_fvar.968` |  |
| 141 | `Svg.MaskEntry.selfMaskId` | Svg.lean:516 | 1 | unknown free variable `_fvar.1136` |  |
| 142 | `Svg.MaskEntry.userUnits` | Svg.lean:504 | 1 | unknown free variable `_fvar.24` |  |
| 143 | `Svg.MaskLink.self_` | Svg.lean:3778 | 1 | frontx: no unfolding equation for LeanSvg.Svg.MaskLink.self_ |  |
| 144 | `Svg.MaskUse.entry` | Svg.lean:525 | 1 | unknown free variable `_fvar.890` |  |
| 145 | `Svg.MaskUse.id` | Svg.lean:524 | 1 | unknown free variable `_fvar.1060` |  |
| 146 | `Svg.MaskUse.mk` | Svg.lean:523 | 1 | frontx: no unfolding equation for LeanSvg.Svg.MaskUse.mk |  |
| 147 | `Svg.Node.shape` | Svg.lean:493 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Node.shape |  |
| 148 | `Svg.Paint.solid` | Svg.lean:41 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Paint.solid |  |
| 149 | `Svg.PaintFallback.color` | Svg.lean:917 | 1 | frontx: no unfolding equation for LeanSvg.Svg.PaintFallback.color |  |
| 150 | `Svg.Shape.mk` | Svg.lean:307 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Shape.mk |  |
| 151 | `Svg.Style.markerMidId` | Svg.lean:300 | 1 | unknown free variable `_fvar.2039` |  |
| 152 | `Svg.Style.markerStartId` | Svg.lean:299 | 1 | unknown free variable `_fvar.2207` |  |
| 153 | `Svg.Style.mk` | Svg.lean:75 | 1 | frontx: no unfolding equation for LeanSvg.Svg.Style.mk |  |
| 154 | `Svg.SubCfg.mk` | Svg.lean:3881 | 1 | frontx: no unfolding equation for LeanSvg.Svg.SubCfg.mk |  |
| 155 | `SvgImage.Entry.mk` | SvgImage.lean:74 | 1 | frontx: no unfolding equation for LeanSvg.SvgImage.Entry.mk |  |
| 156 | `Text.CharPos.mk` | Text.lean:425 | 1 | frontx: no unfolding equation for LeanSvg.Text.CharPos.mk |  |
| 157 | `Text.Cluster.mk` | Text.lean:645 | 1 | frontx: no unfolding equation for LeanSvg.Text.Cluster.mk |  |
| 158 | `Text.DecorRun.mk` | Text.lean:575 | 1 | frontx: no unfolding equation for LeanSvg.Text.DecorRun.mk |  |
| 159 | `Text.ElemPos.mk` | Text.lean:259 | 1 | frontx: no unfolding equation for LeanSvg.Text.ElemPos.mk |  |
| 160 | `Text.Ev.open_` | Text.lean:276 | 1 | frontx: no unfolding equation for LeanSvg.Text.Ev.open_ |  |
| 161 | `Text.Placed.mk` | Text.lean:293 | 1 | frontx: no unfolding equation for LeanSvg.Text.Placed.mk |  |
| 162 | `Text.SpanProps.mk` | Text.lean:191 | 1 | frontx: no unfolding equation for LeanSvg.Text.SpanProps.mk |  |
| 163 | `TextPath.Cub.mk` | TextPath.lean:40 | 1 | frontx: no unfolding equation for LeanSvg.TextPath.Cub.mk |  |
| 164 | `TextPath.Normal.mk` | TextPath.lean:226 | 1 | frontx: no unfolding equation for LeanSvg.TextPath.Normal.mk |  |
| 165 | `TextPath.Seg.mk` | TextPath.lean:91 | 1 | frontx: no unfolding equation for LeanSvg.TextPath.Seg.mk |  |
| 166 | `TextPath.Table.mk` | TextPath.lean:102 | 1 | frontx: no unfolding equation for LeanSvg.TextPath.Table.mk |  |
| 167 | `Turbulence.Axis.mk` | Filter/Turbulence.lean:191 | 1 | frontx: no unfolding equation for LeanSvg.Turbulence.Axis.mk |  |
| 168 | `Turbulence.Params.mk` | Filter/Turbulence.lean:41 | 1 | frontx: no unfolding equation for LeanSvg.Turbulence.Params.mk |  |
| 169 | `Units.Metrics.mk` | Units.lean:40 | 1 | frontx: no unfolding equation for LeanSvg.Units.Metrics.mk |  |
| 170 | `Units.RootLen.mk` | Units.lean:33 | 1 | frontx: no unfolding equation for LeanSvg.Units.RootLen.mk |  |
| 171 | `Use.St.mk` | Use.lean:171 | 1 | frontx: no unfolding equation for LeanSvg.Use.St.mk |  |
| 172 | `Viewport.AspectRatio.mk` | Viewport.lean:27 | 1 | frontx: no unfolding equation for LeanSvg.Viewport.AspectRatio.mk |  |
| 173 | `Xml.Attr.mk` | Xml.lean:36 | 1 | frontx: no unfolding equation for LeanSvg.Xml.Attr.mk |  |
| 174 | `Xml.Attr.name` | Xml.lean:37 | 1 | unknown free variable `_fvar.4212556` |  |
| 175 | `Xml.Scoped.mk` | Xml.lean:85 | 1 | frontx: no unfolding equation for LeanSvg.Xml.Scoped.mk |  |
| 176 | `Xml.Scoped.name` | Xml.lean:87 | 1 | unknown free variable `_fvar.185` |  |
| 177 | `Css.Selector.mk` | Css.lean:80 | 2 | frontx: no unfolding equation for LeanSvg.Css.Selector.mk |  |
| 178 | `Filter.ElemCtx.mk` | Filter.lean:857 | 2 | frontx: no unfolding equation for LeanSvg.Filter.ElemCtx.mk |  |
| 179 | `Filter.Prim.mk` | Filter.lean:234 | 2 | frontx: no unfolding equation for LeanSvg.Filter.Prim.mk |  |
| 180 | `ForeignObject.Item.br` | ForeignObject.lean:80 | 2 | frontx: no unfolding equation for LeanSvg.ForeignObject.Item.br |  |
| 181 | `Grad.RawDef.href` | Shader.lean:356 | 2 | unknown free variable `_fvar.338` |  |
| 182 | `Grad.Shape.linear` | Shader.lean:399 | 2 | frontx: no unfolding equation for LeanSvg.Grad.Shape.linear |  |
| 183 | `Grad.Shape.radial` | Shader.lean:401 | 2 | frontx: no unfolding equation for LeanSvg.Grad.Shape.radial |  |
| 184 | `Jpeg.Huff.mk` | Jpeg/Huffman.lean:41 | 2 | frontx: no unfolding equation for LeanSvg.Jpeg.Huff.mk |  |
| 185 | `JpegDecode.Scan.mk` | JpegDecode.lean:102 | 2 | frontx: no unfolding equation for LeanSvg.JpegDecode.Scan.mk |  |
| 186 | `Options.mk` | Render.lean:23 | 2 | frontx: no unfolding equation for LeanSvg.Options.mk |  |
| 187 | `Pat.RawDef.contentOBB` | Pattern.lean:70 | 2 | unknown free variable `_fvar.149392` |  |
| 188 | `Pat.RawDef.oBB` | Pattern.lean:68 | 2 | unknown free variable `_fvar.766` |  |
| 189 | `PathCmd.quadTo` | Geom.lean:152 | 2 | frontx: no unfolding equation for LeanSvg.PathCmd.quadTo |  |
| 190 | `Shape.Indic.Re.opt` | ShapeRun.lean:545 | 2 | frontx: no unfolding equation for LeanSvg.Shape.Indic.Re.opt |  |
| 191 | `Svg.ClipEntry.id` | Svg.lean:388 | 2 | unknown free variable `_fvar.21026` |  |
| 192 | `Svg.ClipEntry.transformValid` | Svg.lean:393 | 2 | unknown free variable `_fvar.21429` |  |
| 193 | `Svg.GroupInfo.mk` | Svg.lean:457 | 2 | frontx: no unfolding equation for LeanSvg.Svg.GroupInfo.mk |  |
| 194 | `Svg.MaskEntry.alpha` | Svg.lean:506 | 2 | unknown free variable `_fvar.350` |  |
| 195 | `Svg.PaintSpec.solid` | Svg.lean:925 | 2 | frontx: no unfolding equation for LeanSvg.Svg.PaintSpec.solid |  |
| 196 | `Svg.SpanLayers.mk` | Svg.lean:3197 | 2 | frontx: no unfolding equation for LeanSvg.Svg.SpanLayers.mk |  |
| 197 | `Use.mkAttr` | Use.lean:161 | 2 | unknown free variable `_fvar.1927109` |  |
| 198 | `Xml.Event.open_` | Xml.lean:42 | 2 | frontx: no unfolding equation for LeanSvg.Xml.Event.open_ |  |
| 199 | `BasicShape.Radius.lp` | BasicShape.lean:56 | 3 | frontx: no unfolding equation for LeanSvg.BasicShape.Radius.lp |  |
| 200 | `Css.AttrOp.startsWithDash` | Css.lean:50 | 3 | frontx: no unfolding equation for LeanSvg.Css.AttrOp.startsWithDash |  |
| 201 | `Css.Component.comp` | Css.lean:77 | 3 | unknown free variable `_fvar.81` |  |
| 202 | `Css.Component.mk` | Css.lean:73 | 3 | frontx: no unfolding equation for LeanSvg.Css.Component.mk |  |
| 203 | `Css.Decl.important` | Css.lean:89 | 3 | unknown free variable `_fvar.499` |  |
| 204 | `Filter.Kind.displacementMap` | Filter.lean:212 | 3 | frontx: no unfolding equation for LeanSvg.Filter.Kind.displacementMap |  |
| 205 | `Filter.Len.pct` | Filter.lean:428 | 3 | frontx: no unfolding equation for LeanSvg.Filter.Len.pct |  |
| 206 | `Filter.RawFilter.hasChildren` | Filter.lean:293 | 3 | unknown free variable `_fvar.264` |  |
| 207 | `Grad.Built.solid` | Shader.lean:882 | 3 | frontx: no unfolding equation for LeanSvg.Grad.Built.solid |  |
| 208 | `Grad.RtStop.mk` | Shader.lean:615 | 3 | frontx: no unfolding equation for LeanSvg.Grad.RtStop.mk |  |
| 209 | `Pat.RawDef.hadChildren` | Pattern.lean:90 | 3 | unknown free variable `_fvar.45` |  |
| 210 | `Pat.RawDef.href` | Pattern.lean:65 | 3 | unknown free variable `_fvar.404` |  |
| 211 | `Svg.MarkerEntry.unitsUser` | Svg.lean:568 | 3 | unknown free variable `_fvar.55` |  |
| 212 | `Svg.MarkerOrient.fixed` | Svg.lean:545 | 3 | frontx: no unfolding equation for LeanSvg.Svg.MarkerOrient.fixed |  |
| 213 | `Svg.MaskLink.use` | Svg.lean:3779 | 3 | frontx: no unfolding equation for LeanSvg.Svg.MaskLink.use |  |
| 214 | `Svg.PaintSpec.url` | Svg.lean:927 | 3 | frontx: no unfolding equation for LeanSvg.Svg.PaintSpec.url |  |
| 215 | `Svg.RootInfo.mk` | Svg.lean:440 | 3 | frontx: no unfolding equation for LeanSvg.Svg.RootInfo.mk |  |
| 216 | `Svg.Style.markerEndId` | Svg.lean:301 | 3 | unknown free variable `_fvar.1871` |  |
| 217 | `Svg.Style.maskRef` | Svg.lean:289 | 3 | unknown free variable `_fvar.170` |  |
| 218 | `BasicShape.Geo.rect` | BasicShape.lean:64 | 4 | frontx: no unfolding equation for LeanSvg.BasicShape.Geo.rect |  |
| 219 | `Filter.Kind.convolveMatrix` | Filter.lean:206 | 4 | frontx: no unfolding equation for LeanSvg.Filter.Kind.convolveMatrix |  |
| 220 | `Filter.Outcome.filters` | Filter.lean:853 | 4 | frontx: no unfolding equation for LeanSvg.Filter.Outcome.filters |  |
| 221 | `Filter.RawPrim.color` | Filter.lean:279 | 4 | unknown free variable `_fvar.221` |  |
| 222 | `Pat.RawDef.aspect` | Pattern.lean:86 | 4 | unknown free variable `_fvar.149201` |  |
| 223 | `Svg.ClipEntry.objectBBox` | Svg.lean:395 | 4 | unknown free variable `_fvar.21043` |  |
| 224 | `Svg.MaskEntry.filled` | Svg.lean:519 | 4 | unknown free variable `_fvar.396` |  |
| 225 | `Svg.PaintSpec.context` | Svg.lean:930 | 4 | frontx: no unfolding equation for LeanSvg.Svg.PaintSpec.context |  |
| 226 | `Svg.Style.clipRef` | Svg.lean:254 | 4 | unknown free variable `_fvar.715` |  |
| 227 | `Svg.inlinePathKey` | Svg.lean:3058 | 4 | unknown free variable `_fvar.549790` |  |
| 228 | `BasicShape.Geo.path` | BasicShape.lean:69 | 5 | frontx: no unfolding equation for LeanSvg.BasicShape.Geo.path |  |
| 229 | `Css.Compound.firstChild` | Css.lean:59 | 5 | unknown free variable `_fvar.112` |  |
| 230 | `Css.ElemInfo.isFirstChild` | Css.lean:103 | 5 | unknown free variable `_fvar.14` |  |
| 231 | `FeImage.Href.data` | Filter/Image.lean:43 | 5 | frontx: no unfolding equation for LeanSvg.FeImage.Href.data |  |
| 232 | `Filter.TF.gamma` | Filter.lean:181 | 5 | frontx: no unfolding equation for LeanSvg.Filter.TF.gamma |  |
| 233 | `Filter.UrlRes.ok` | Filter.lean:870 | 5 | frontx: no unfolding equation for LeanSvg.Filter.UrlRes.ok |  |
| 234 | `ForeignObject.Item.bgStart` | ForeignObject.lean:82 | 5 | frontx: no unfolding equation for LeanSvg.ForeignObject.Item.bgStart |  |
| 235 | `Lighting.Light.spot` | Filter/Lighting.lean:38 | 5 | frontx: no unfolding equation for LeanSvg.Lighting.Light.spot |  |
| 236 | `Mask.Res.chain` | Mask.lean:49 | 5 | frontx: no unfolding equation for LeanSvg.Mask.Res.chain |  |
| 237 | `Pat.Built.tile` | PatternRender.lean:86 | 5 | frontx: no unfolding equation for LeanSvg.Pat.Built.tile |  |
| 238 | `Pat.Resolved.mk` | Pattern.lean:104 | 5 | frontx: no unfolding equation for LeanSvg.Pat.Resolved.mk |  |
| 239 | `Svg.MarkerEntry.clipEntryIdx` | Svg.lean:577 | 5 | unknown free variable `_fvar.827` |  |
| 240 | `Svg.MarkerEntry.valid` | Svg.lean:582 | 5 | unknown free variable `_fvar.80` |  |
| 241 | `Clip.Res.chain` | Clip.lean:247 | 6 | frontx: no unfolding equation for LeanSvg.Clip.Res.chain |  |
| 242 | `Filter.Input.ref` | Filter.lean:162 | 6 | frontx: no unfolding equation for LeanSvg.Filter.Input.ref |  |
| 243 | `Grad.Built.grad` | Shader.lean:885 | 6 | frontx: no unfolding equation for LeanSvg.Grad.Built.grad |  |
| 244 | `Svg.ClipEntry.filled` | Svg.lean:404 | 6 | unknown free variable `_fvar.20856` |  |
| 245 | `Svg.MarkerEntry.clip` | Svg.lean:571 | 6 | unknown free variable `_fvar.627` |  |
| 246 | `Svg.Paint.gradient` | Svg.lean:42 | 6 | frontx: no unfolding equation for LeanSvg.Svg.Paint.gradient |  |
| 247 | `Css.Compound.valid` | Css.lean:64 | 7 | unknown free variable `_fvar.488` |  |
| 248 | `Svg.MarkerEntry.filled` | Svg.lean:591 | 7 | unknown free variable `_fvar.858` |  |
| 249 | `Text.Ev.openPath` | Text.lean:277 | 7 | frontx: no unfolding equation for LeanSvg.Text.Ev.openPath |  |
| 250 | `Use.fmtFixed` | Use.lean:150 | 7 | unknown free variable `_fvar.777271` |  |
| 251 | `Filter.CMKind.hueRotate` | Filter.lean:170 | 8 | frontx: no unfolding equation for LeanSvg.Filter.CMKind.hueRotate |  |
| 252 | `Filter.CompOp.arith` | Filter.lean:186 | 8 | frontx: no unfolding equation for LeanSvg.Filter.CompOp.arith |  |
| 253 | `Svg.Node.groupBegin` | Svg.lean:494 | 8 | frontx: no unfolding equation for LeanSvg.Svg.Node.groupBegin |  |
| 254 | `Svg.OriginTok.len` | Svg.lean:1589 | 8 | frontx: no unfolding equation for LeanSvg.Svg.OriginTok.len |  |
| 255 | `Text.Ev.text` | Text.lean:284 | 9 | frontx: no unfolding equation for LeanSvg.Text.Ev.text |  |
| 256 | `Warn.quote` | Warn.lean:34 | 9 | unknown free variable `_fvar.6175` |  |
| 257 | `Clip.Key.mk` | Clip.lean:253 | 10 | frontx: no unfolding equation for LeanSvg.Clip.Key.mk |  |
| 258 | `Xml.nsLookup` | Xml.lean:75 | 10 | unknown free variable `_fvar.340263` |  |
| 259 | `Pat.RawDef.eventIdx` | Pattern.lean:93 | 11 | unknown free variable `_fvar.23` |  |
| 260 | `Svg.ClipMode.markerDef` | Svg.lean:3668 | 11 | frontx: no unfolding equation for LeanSvg.Svg.ClipMode.markerDef |  |
| 261 | `Grad.Geom.conical` | Shader.lean:636 | 20 | frontx: no unfolding equation for LeanSvg.Grad.Geom.conical |  |
| 262 | `Xml.Event.text` | Xml.lean:44 | 23 | frontx: no unfolding equation for LeanSvg.Xml.Event.text |  |
| 263 | `Svg.Paint.pattern` | Svg.lean:48 | 27 | frontx: no unfolding equation for LeanSvg.Svg.Paint.pattern |  |
| 264 | `Bytes.toStr` | Bytes.lean:107 | ? | unknown free variable `_fvar.304759` |  |
| 265 | `FontSet.Entry.coverage` | FontSet.lean:83 | ? | unknown free variable `_fvar.53509` |  |
| 266 | `Warn.missingFont` | Warn.lean:43 | ? | unknown free variable `_fvar.5467` |  |

### 1.2 user structure / inductive as parameter or result

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Grad.instBEqKind.beq` | Shader.lean:336 | 0 | frontx: unsupported parameter type LeanSvg.Grad.Kind |  |
| 2 | `Image.instBEqFmt.beq` | Image.lean:208 | 0 | frontx: unsupported parameter type LeanSvg.Image.Fmt |  |
| 3 | `Text.instBEqAlignmentBaseline.beq` | Baseline.lean:74 | 0 | frontx: unsupported parameter type LeanSvg.Text.AlignmentBaseline |  |
| 4 | `instBEqCap.beq` | Geom.lean:480 | 0 | frontx: unsupported parameter type LeanSvg.Cap |  |
| 5 | `BasicShape.Spec.geo` | BasicShape.lean:75 | 1 | frontx: unsupported result type LeanSvg.BasicShape.Geo |  |
| 6 | `Brotli.Blocks.counts` | Brotli.lean:244 | 1 | frontx: unsupported result type LeanSvg.Brotli.Code |  |
| 7 | `Brotli.Blocks.cur` | Brotli.lean:245 | 1 | frontx: unsupported parameter type LeanSvg.Brotli.Blocks |  |
| 8 | `Brotli.Blocks.last2` | Brotli.lean:246 | 1 | frontx: unsupported parameter type LeanSvg.Brotli.Blocks |  |
| 9 | `Brotli.Blocks.n` | Brotli.lean:242 | 1 | frontx: unsupported parameter type LeanSvg.Brotli.Blocks |  |
| 10 | `Brotli.Blocks.types` | Brotli.lean:243 | 1 | frontx: unsupported result type LeanSvg.Brotli.Code |  |
| 11 | `Brotli.Code.single` | Brotli.lean:63 | 1 | frontx: unsupported parameter type LeanSvg.Brotli.Code |  |
| 12 | `Canvas.h` | Canvas.lean:25 | 1 | frontx: unsupported parameter type LeanSvg.Canvas |  |
| 13 | `Canvas.w` | Canvas.lean:24 | 1 | frontx: unsupported parameter type LeanSvg.Canvas |  |
| 14 | `Clip.Mask.h` | Clip.lean:90 | 1 | frontx: unsupported parameter type LeanSvg.Clip.Mask |  |
| 15 | `Clip.Mask.w` | Clip.lean:89 | 1 | frontx: unsupported parameter type LeanSvg.Clip.Mask |  |
| 16 | `Clip.Mask.x0` | Clip.lean:87 | 1 | frontx: unsupported parameter type LeanSvg.Clip.Mask |  |
| 17 | `Clip.Mask.y0` | Clip.lean:88 | 1 | frontx: unsupported parameter type LeanSvg.Clip.Mask |  |
| 18 | `Css.Component.comb` | Css.lean:76 | 1 | frontx: unsupported result type LeanSvg.Css.Combinator |  |
| 19 | `Css.Rule.selector` | Css.lean:93 | 1 | frontx: unsupported result type LeanSvg.Css.Selector |  |
| 20 | `FeImage.Job.prim` | Filter/ImageRender.lean:18 | 1 | frontx: unsupported parameter type LeanSvg.FeImage.Job |  |
| 21 | `FeImage.Job.rh` | Filter/ImageRender.lean:21 | 1 | frontx: unsupported parameter type LeanSvg.FeImage.Job |  |
| 22 | `FeImage.Job.rw` | Filter/ImageRender.lean:20 | 1 | frontx: unsupported parameter type LeanSvg.FeImage.Job |  |
| 23 | `FeImage.Job.spec` | Filter/ImageRender.lean:19 | 1 | frontx: unsupported result type LeanSvg.FeImage.Spec |  |
| 24 | `FeImage.Spec.href` | Filter/Image.lean:49 | 1 | frontx: unsupported result type LeanSvg.FeImage.Href |  |
| 25 | `Filter.ElemCtx.color` | Filter.lean:861 | 1 | frontx: unsupported parameter type LeanSvg.Filter.ElemCtx |  |
| 26 | `Filter.Prim.linear` | Filter.lean:238 | 1 | frontx: unsupported parameter type LeanSvg.Filter.Prim |  |
| 27 | `Filter.Resolved.region` | Filter.lean:248 | 1 | frontx: unsupported result type LeanSvg.Filter.URect |  |
| 28 | `FilterApply.Img.cv` | FilterApply.lean:107 | 1 | frontx: unsupported result type LeanSvg.Canvas |  |
| 29 | `FilterFrame.Plan.w` | FilterFrame.lean:53 | 1 | frontx: unsupported parameter type LeanSvg.FilterFrame.Plan |  |
| 30 | `Font.cmapSorted` | Font.lean:81 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 31 | `Font.glyfOff` | Font.lean:73 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 32 | `Font.indexToLocFormat` | Font.lean:71 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 33 | `Font.kernPairsOff` | Font.lean:87 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 34 | `Font.locaOff` | Font.lean:72 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 35 | `Font.numberOfHMetrics` | Font.lean:82 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 36 | `Font.tailChunkBytes` | Font.lean:110 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 37 | `Font.unitsPerEm` | Font.lean:43 | 1 | frontx: unsupported parameter type LeanSvg.Font |  |
| 38 | `FontFace.Face.font` | FontFace.lean:50 | 1 | frontx: unsupported result type LeanSvg.Font |  |
| 39 | `FontFace.Face.italic` | FontFace.lean:49 | 1 | frontx: unsupported parameter type LeanSvg.FontFace.Face |  |
| 40 | `FontFace.Face.weight` | FontFace.lean:48 | 1 | frontx: unsupported parameter type LeanSvg.FontFace.Face |  |
| 41 | `ForeignObject.HStyle.italic` | ForeignObject.lean:68 | 1 | frontx: unsupported parameter type LeanSvg.ForeignObject.HStyle |  |
| 42 | `ForeignObject.HStyle.weight` | ForeignObject.lean:67 | 1 | frontx: unsupported parameter type LeanSvg.ForeignObject.HStyle |  |
| 43 | `ForeignObject.HStyle.wrap` | ForeignObject.lean:75 | 1 | frontx: unsupported parameter type LeanSvg.ForeignObject.HStyle |  |
| 44 | `Grad.Axis.aL` | Shader.lean:660 | 1 | frontx: unsupported parameter type LeanSvg.Grad.Axis |  |
| 45 | `Grad.Axis.cL` | Shader.lean:661 | 1 | frontx: unsupported parameter type LeanSvg.Grad.Axis |  |
| 46 | `Grad.RawDef.kind` | Shader.lean:355 | 1 | frontx: unsupported result type LeanSvg.Grad.Kind |  |
| 47 | `Grad.RawStop.col` | Shader.lean:342 | 1 | frontx: unsupported parameter type LeanSvg.Grad.RawStop |  |
| 48 | `Grad.Resolved.oBB` | Shader.lean:407 | 1 | frontx: unsupported parameter type LeanSvg.Grad.Resolved |  |
| 49 | `Grad.Resolved.shape` | Shader.lean:406 | 1 | frontx: unsupported result type LeanSvg.Grad.Shape |  |
| 50 | `Grad.Resolved.spread` | Shader.lean:409 | 1 | frontx: unsupported result type LeanSvg.Grad.Spread |  |
| 51 | `Grad.Rt.geom` | Shader.lean:679 | 1 | frontx: unsupported result type LeanSvg.Grad.Geom |  |
| 52 | `Grad.Rt.px` | Shader.lean:682 | 1 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 53 | `Grad.Rt.py` | Shader.lean:683 | 1 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 54 | `Image.Pix.h` | Image.lean:231 | 1 | frontx: unsupported parameter type LeanSvg.Image.Pix |  |
| 55 | `Image.Pix.w` | Image.lean:230 | 1 | frontx: unsupported parameter type LeanSvg.Image.Pix |  |
| 56 | `Image.Placed.pix` | Image.lean:299 | 1 | frontx: unsupported result type LeanSvg.Image.Pix |  |
| 57 | `Image.Rt.pix` | Image.lean:353 | 1 | frontx: unsupported result type LeanSvg.Image.Pix |  |
| 58 | `Image.Rt.px` | Image.lean:354 | 1 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 59 | `Image.Rt.py` | Image.lean:355 | 1 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 60 | `Inflate.Huff.bits` | Inflate.lean:36 | 1 | frontx: unsupported parameter type LeanSvg.Inflate.Huff |  |
| 61 | `JpegDecode.Frame.h` | JpegDecode.lean:95 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 62 | `JpegDecode.Frame.hmax` | JpegDecode.lean:97 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 63 | `JpegDecode.Frame.mcux` | JpegDecode.lean:99 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 64 | `JpegDecode.Frame.prog` | JpegDecode.lean:93 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 65 | `JpegDecode.Frame.vmax` | JpegDecode.lean:98 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 66 | `JpegDecode.Frame.w` | JpegDecode.lean:94 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 67 | `JpegDecode.Scan.ah` | JpegDecode.lean:107 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Scan |  |
| 68 | `JpegDecode.Scan.se` | JpegDecode.lean:106 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Scan |  |
| 69 | `JpegDecode.Scan.ss` | JpegDecode.lean:105 | 1 | frontx: unsupported parameter type LeanSvg.JpegDecode.Scan |  |
| 70 | `Lighting.Params.b` | Filter/Lighting.lean:50 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 71 | `Lighting.Params.g` | Filter/Lighting.lean:49 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 72 | `Lighting.Params.k` | Filter/Lighting.lean:46 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 73 | `Lighting.Params.r` | Filter/Lighting.lean:48 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 74 | `Lighting.Params.se` | Filter/Lighting.lean:47 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 75 | `Lighting.Params.specular` | Filter/Lighting.lean:44 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 76 | `Lighting.Params.ss` | Filter/Lighting.lean:45 | 1 | frontx: unsupported parameter type LeanSvg.Lighting.Params |  |
| 77 | `Mask.Step.entry` | Mask.lean:40 | 1 | frontx: unsupported parameter type LeanSvg.Mask.Step |  |
| 78 | `Mask.Step.region` | Mask.lean:41 | 1 | frontx: unsupported result type LeanSvg.Box |  |
| 79 | `Pat.Resolved.alignX` | Pattern.lean:118 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 80 | `Pat.Resolved.alignY` | Pattern.lean:119 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 81 | `Pat.Resolved.contentOBB` | Pattern.lean:111 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 82 | `Pat.Resolved.oBB` | Pattern.lean:110 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 83 | `Pat.Resolved.slice` | Pattern.lean:120 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 84 | `Pat.Resolved.valid` | Pattern.lean:109 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 85 | `Pat.Rt.cv` | PatternRender.lean:72 | 1 | frontx: unsupported result type LeanSvg.Canvas |  |
| 86 | `Pat.Rt.px` | PatternRender.lean:73 | 1 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 87 | `Pat.Rt.tileH` | PatternRender.lean:71 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Rt |  |
| 88 | `Pat.Rt.tileW` | PatternRender.lean:70 | 1 | frontx: unsupported parameter type LeanSvg.Pat.Rt |  |
| 89 | `PngDecode.Meta.hdr` | PngDecode.lean:71 | 1 | frontx: unsupported parameter type LeanSvg.PngDecode.Meta |  |
| 90 | `Raster.Mask.w` | Raster.lean:68 | 1 | frontx: unsupported parameter type LeanSvg.Raster.Mask |  |
| 91 | `Raster.Mask.x0` | Raster.lean:66 | 1 | frontx: unsupported parameter type LeanSvg.Raster.Mask |  |
| 92 | `Raster.Mask.y0` | Raster.lean:67 | 1 | frontx: unsupported parameter type LeanSvg.Raster.Mask |  |
| 93 | `Render.Clip.x0` | Render.lean:61 | 1 | frontx: unsupported parameter type LeanSvg.Render.Clip |  |
| 94 | `Render.Clip.x1` | Render.lean:63 | 1 | frontx: unsupported parameter type LeanSvg.Render.Clip |  |
| 95 | `Render.Clip.y0` | Render.lean:62 | 1 | frontx: unsupported parameter type LeanSvg.Render.Clip |  |
| 96 | `Render.Layer.cache` | Render.lean:504 | 1 | frontx: unsupported result type LeanSvg.Clip.Cache |  |
| 97 | `Render.Layer.clip` | Render.lean:481 | 1 | frontx: unsupported result type LeanSvg.Render.Clip |  |
| 98 | `Render.Layer.cv` | Render.lean:478 | 1 | frontx: unsupported result type LeanSvg.Canvas |  |
| 99 | `Render.Layer.fh` | Render.lean:503 | 1 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 100 | `Render.Layer.fw` | Render.lean:502 | 1 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 101 | `Render.Layer.opacityQ` | Render.lean:484 | 1 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 102 | `Render.Layer.ox` | Render.lean:479 | 1 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 103 | `Render.Layer.oy` | Render.lean:480 | 1 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 104 | `Render.Target.clip` | Render.lean:222 | 1 | frontx: unsupported result type LeanSvg.Render.Clip |  |
| 105 | `Render.Target.h` | Render.lean:221 | 1 | frontx: unsupported parameter type LeanSvg.Render.Target |  |
| 106 | `Render.Target.ox` | Render.lean:223 | 1 | frontx: unsupported parameter type LeanSvg.Render.Target |  |
| 107 | `Render.Target.w` | Render.lean:220 | 1 | frontx: unsupported parameter type LeanSvg.Render.Target |  |
| 108 | `Shape.Indic.Cfg.abvf` | ShapeRun.lean:719 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 109 | `Shape.Indic.Cfg.blwf` | ShapeRun.lean:718 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 110 | `Shape.Indic.Cfg.font` | ShapeRun.lean:714 | 1 | frontx: unsupported result type LeanSvg.Font |  |
| 111 | `Shape.Indic.Cfg.half` | ShapeRun.lean:717 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 112 | `Shape.Indic.Cfg.init` | ShapeRun.lean:722 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 113 | `Shape.Indic.Cfg.lay` | ShapeRun.lean:713 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 114 | `Shape.Indic.Cfg.oldSpec` | ShapeRun.lean:715 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 115 | `Shape.Indic.Cfg.plan` | ShapeRun.lean:712 | 1 | frontx: unsupported result type LeanSvg.Shape.Plan |  |
| 116 | `Shape.Indic.Cfg.pref` | ShapeRun.lean:721 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 117 | `Shape.Indic.Cfg.pstf` | ShapeRun.lean:720 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 118 | `Shape.Indic.Cfg.rphf` | ShapeRun.lean:716 | 1 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 119 | `Shape.St.autoZwj` | Shape.lean:488 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 120 | `Shape.St.autoZwnj` | Shape.lean:489 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 121 | `Shape.St.haveOutput` | Shape.lean:481 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 122 | `Shape.St.idx` | Shape.lean:480 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 123 | `Shape.St.isGpos` | Shape.lean:476 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 124 | `Shape.St.lay` | Shape.lean:475 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 125 | `Shape.St.lookupMask` | Shape.lean:486 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 126 | `Shape.St.lookupProps` | Shape.lean:487 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 127 | `Shape.St.maxLen` | Shape.lean:484 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 128 | `Shape.St.ok` | Shape.lean:482 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 129 | `Shape.St.ops` | Shape.lean:483 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 130 | `Shape.St.perSyl` | Shape.lean:490 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 131 | `Shape.St.serial` | Shape.lean:485 | 1 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 132 | `StrokeStyle.cap` | Geom.lean:488 | 1 | frontx: unsupported result type LeanSvg.Cap |  |
| 133 | `Svg.ClipChild.evenOdd` | Svg.lean:373 | 1 | frontx: unsupported parameter type LeanSvg.Svg.ClipChild |  |
| 134 | `Svg.DefsScan.pctRef` | Svg.lean:2866 | 1 | frontx: unsupported result type LeanSvg.Grad.PctRef |  |
| 135 | `Svg.Doc.patterns` | Svg.lean:618 | 1 | frontx: unsupported result type LeanSvg.Pat.Defs |  |
| 136 | `Svg.Doc.root` | Svg.lean:599 | 1 | frontx: unsupported result type LeanSvg.Svg.RootInfo |  |
| 137 | `Svg.GroupInfo.blend` | Svg.lean:460 | 1 | frontx: unsupported result type LeanSvg.BlendMode |  |
| 138 | `Svg.GroupInfo.opacity` | Svg.lean:459 | 1 | frontx: unsupported parameter type LeanSvg.Svg.GroupInfo |  |
| 139 | `Svg.Style.cap` | Svg.lean:82 | 1 | frontx: unsupported result type LeanSvg.Cap |  |
| 140 | `Svg.Style.ctxFill` | Svg.lean:270 | 1 | frontx: unsupported result type LeanSvg.Svg.Paint |  |
| 141 | `Svg.Style.dominantBaseline` | Svg.lean:205 | 1 | frontx: unsupported result type LeanSvg.Text.AlignmentBaseline |  |
| 142 | `Svg.Style.evenOdd` | Svg.lean:78 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 143 | `Svg.Style.fill` | Svg.lean:76 | 1 | frontx: unsupported result type LeanSvg.Svg.Paint |  |
| 144 | `Svg.Style.fillCtx` | Svg.lean:278 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 145 | `Svg.Style.fillCtxKind` | Svg.lean:286 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 146 | `Svg.Style.fillOpacity` | Svg.lean:77 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 147 | `Svg.Style.fontStretch` | Svg.lean:179 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 148 | `Svg.Style.isolate` | Svg.lean:109 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 149 | `Svg.Style.join` | Svg.lean:83 | 1 | frontx: unsupported result type LeanSvg.Join |  |
| 150 | `Svg.Style.ownOverline` | Svg.lean:231 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 151 | `Svg.Style.ownUnderline` | Svg.lean:230 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 152 | `Svg.Style.patterns` | Svg.lean:156 | 1 | frontx: unsupported result type LeanSvg.Pat.Defs |  |
| 153 | `Svg.Style.stroke` | Svg.lean:79 | 1 | frontx: unsupported result type LeanSvg.Svg.Paint |  |
| 154 | `Svg.Style.strokeOpacity` | Svg.lean:80 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 155 | `Svg.Style.textKerning` | Svg.lean:189 | 1 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 156 | `Text.Cluster.cp` | Text.lean:646 | 1 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 157 | `Text.Cluster.font` | Text.lean:664 | 1 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 158 | `Text.Cluster.styleIdx` | Text.lean:647 | 1 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 159 | `Text.DecorRun.styleIdx` | Text.lean:576 | 1 | frontx: unsupported parameter type LeanSvg.Text.DecorRun |  |
| 160 | `Text.DecorRun.unitsPerEm` | Text.lean:581 | 1 | frontx: unsupported parameter type LeanSvg.Text.DecorRun |  |
| 161 | `Text.Placed.styleIdx` | Text.lean:294 | 1 | frontx: unsupported parameter type LeanSvg.Text.Placed |  |
| 162 | `Text.SpanProps.baselineShiftSub` | Text.lean:221 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 163 | `Text.SpanProps.dominantBaseline` | Text.lean:214 | 1 | frontx: unsupported result type LeanSvg.Text.AlignmentBaseline |  |
| 164 | `Text.SpanProps.family` | Text.lean:202 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 165 | `Text.SpanProps.kerning` | Text.lean:210 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 166 | `Text.SpanProps.overlineIdx` | Text.lean:230 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 167 | `Text.SpanProps.underlineIdx` | Text.lean:229 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 168 | `Text.SpanProps.weight` | Text.lean:195 | 1 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 169 | `TextPath.Seg.c` | TextPath.lean:92 | 1 | frontx: unsupported result type LeanSvg.TextPath.Cub |  |
| 170 | `TextPath.Seg.n` | TextPath.lean:93 | 1 | frontx: unsupported parameter type LeanSvg.TextPath.Seg |  |
| 171 | `Turbulence.Params.fxD` | Filter/Turbulence.lean:43 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 172 | `Turbulence.Params.fxN` | Filter/Turbulence.lean:42 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 173 | `Turbulence.Params.fyD` | Filter/Turbulence.lean:45 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 174 | `Turbulence.Params.fyN` | Filter/Turbulence.lean:44 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 175 | `Turbulence.Params.octaves` | Filter/Turbulence.lean:46 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 176 | `Turbulence.Params.stitch` | Filter/Turbulence.lean:48 | 1 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 177 | `Use.St.work` | Use.lean:174 | 1 | frontx: unsupported parameter type LeanSvg.Use.St |  |
| 178 | `Xml.Scoped.html` | Xml.lean:90 | 1 | frontx: unsupported parameter type LeanSvg.Xml.Scoped |  |
| 179 | `Bidi.instBEqCls.beq` | Bidi.lean:63 | 2 | frontx: unsupported parameter type LeanSvg.Bidi.Cls |  |
| 180 | `Filter.Parsers.opOne` | Filter.lean:306 | 2 | frontx: unsupported parameter type LeanSvg.Filter.Parsers |  |
| 181 | `Filter.Prim.sub` | Filter.lean:236 | 2 | frontx: unsupported result type LeanSvg.Filter.URect |  |
| 182 | `FilterFrame.Plan.h` | FilterFrame.lean:54 | 2 | frontx: unsupported parameter type LeanSvg.FilterFrame.Plan |  |
| 183 | `Font.cmapOff` | Font.lean:76 | 2 | frontx: unsupported parameter type LeanSvg.Font |  |
| 184 | `Font.glyfLen` | Font.lean:74 | 2 | frontx: unsupported parameter type LeanSvg.Font |  |
| 185 | `Font.hmtxOff` | Font.lean:83 | 2 | frontx: unsupported parameter type LeanSvg.Font |  |
| 186 | `Font.maxPointsCap` | Font.lean:85 | 2 | frontx: unsupported parameter type LeanSvg.Font |  |
| 187 | `Grad.Rt.spread` | Shader.lean:680 | 2 | frontx: unsupported result type LeanSvg.Grad.Spread |  |
| 188 | `JpegDecode.Frame.mcuy` | JpegDecode.lean:100 | 2 | frontx: unsupported parameter type LeanSvg.JpegDecode.Frame |  |
| 189 | `Options.width` | Render.lean:25 | 2 | frontx: unsupported parameter type LeanSvg.Options |  |
| 190 | `Raster.Mask.h` | Raster.lean:69 | 2 | frontx: unsupported parameter type LeanSvg.Raster.Mask |  |
| 191 | `Render.Layer.opacity` | Render.lean:482 | 2 | frontx: unsupported parameter type LeanSvg.Render.Layer |  |
| 192 | `Shape.Indic.Cfg.virama` | ShapeRun.lean:723 | 2 | frontx: unsupported parameter type LeanSvg.Shape.Indic.Cfg |  |
| 193 | `Shape.instBEqMatch.beq` | Shape.lean:675 | 2 | frontx: unsupported parameter type LeanSvg.Shape.Match |  |
| 194 | `Shape.instBEqShaper.beq` | ShapeRun.lean:87 | 2 | frontx: unsupported parameter type LeanSvg.Shape.Shaper |  |
| 195 | `StrokeStyle.join` | Geom.lean:489 | 2 | frontx: unsupported result type LeanSvg.Join |  |
| 196 | `Svg.Frame.filterAt` | Svg.lean:3728 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 197 | `Svg.Frame.filterOnly` | Svg.lean:3730 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 198 | `Svg.Frame.want` | Svg.lean:3709 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 199 | `Svg.GroupInfo.passthrough` | Svg.lean:479 | 2 | frontx: unsupported parameter type LeanSvg.Svg.GroupInfo |  |
| 200 | `Svg.Style.blend` | Svg.lean:107 | 2 | frontx: unsupported result type LeanSvg.BlendMode |  |
| 201 | `Svg.Style.fontSmallCaps` | Svg.lean:177 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 202 | `Svg.Style.fontWeight` | Svg.lean:172 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 203 | `Svg.Style.lang` | Svg.lean:247 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 204 | `Svg.Style.maskAlpha` | Svg.lean:292 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 205 | `Svg.Style.ownBidiOverride` | Svg.lean:243 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 206 | `Svg.Style.ownLengthAdjustGlyphs` | Svg.lean:239 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 207 | `Svg.Style.rootFontSize` | Svg.lean:170 | 2 | frontx: unsupported result type LeanSvg.Units.RootLen |  |
| 208 | `Svg.Style.spacePreserve` | Svg.lean:245 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 209 | `Svg.Style.strokeCtxKind` | Svg.lean:287 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 210 | `Svg.Style.textRtl` | Svg.lean:241 | 2 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 211 | `SvgImage.Entry.layerDepth` | SvgImage.lean:78 | 2 | frontx: unsupported parameter type LeanSvg.SvgImage.Entry |  |
| 212 | `Text.Cluster.props` | Text.lean:648 | 2 | frontx: unsupported result type LeanSvg.Text.SpanProps |  |
| 213 | `Text.SpanProps.italic` | Text.lean:196 | 2 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 214 | `Text.SpanProps.smallCaps` | Text.lean:200 | 2 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 215 | `Text.SpanProps.stretch` | Text.lean:198 | 2 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 216 | `Units.Metrics.ideo` | Units.lean:46 | 2 | frontx: unsupported parameter type LeanSvg.Units.Metrics |  |
| 217 | `Units.Metrics.zero` | Units.lean:44 | 2 | frontx: unsupported parameter type LeanSvg.Units.Metrics |  |
| 218 | `Use.St.maxClips` | Use.lean:180 | 2 | frontx: unsupported parameter type LeanSvg.Use.St |  |
| 219 | `Xml.Scoped.foreign` | Xml.lean:88 | 2 | frontx: unsupported parameter type LeanSvg.Xml.Scoped |  |
| 220 | `BasicShape.instBEqRefBox.beq` | BasicShape.lean:53 | 3 | frontx: unsupported parameter type LeanSvg.BasicShape.RefBox |  |
| 221 | `Brotli.Blocks.left` | Brotli.lean:247 | 3 | frontx: unsupported parameter type LeanSvg.Brotli.Blocks |  |
| 222 | `Css.Rule.sourceOrder` | Css.lean:95 | 3 | frontx: unsupported parameter type LeanSvg.Css.Rule |  |
| 223 | `Css.Selector.valid` | Css.lean:83 | 3 | frontx: unsupported parameter type LeanSvg.Css.Selector |  |
| 224 | `FeImage.Spec.aspect` | Filter/Image.lean:50 | 3 | frontx: unsupported result type LeanSvg.Viewport.AspectRatio |  |
| 225 | `FeImage.Spec.quality` | Filter/Image.lean:53 | 3 | frontx: unsupported result type LeanSvg.Image.Quality |  |
| 226 | `Filter.Prim.kind` | Filter.lean:239 | 3 | frontx: unsupported result type LeanSvg.Filter.Kind |  |
| 227 | `FilterApply.Img.lin` | FilterApply.lean:112 | 3 | frontx: unsupported parameter type LeanSvg.FilterApply.Img |  |
| 228 | `FilterFrame.Plan.back` | FilterFrame.lean:59 | 3 | frontx: unsupported result type LeanSvg.FilterFrame.Back |  |
| 229 | `Font.cmapFormat` | Font.lean:78 | 3 | frontx: unsupported parameter type LeanSvg.Font |  |
| 230 | `Font.kernNPairs` | Font.lean:88 | 3 | frontx: unsupported parameter type LeanSvg.Font |  |
| 231 | `ForeignObject.HStyle.align` | ForeignObject.lean:71 | 3 | frontx: unsupported parameter type LeanSvg.ForeignObject.HStyle |  |
| 232 | `ForeignObject.Line.st` | ForeignObject.lean:254 | 3 | frontx: unsupported result type LeanSvg.ForeignObject.HStyle |  |
| 233 | `Grad.Axis.eL` | Shader.lean:662 | 3 | frontx: unsupported parameter type LeanSvg.Grad.Axis |  |
| 234 | `Image.Placed.quality` | Image.lean:304 | 3 | frontx: unsupported result type LeanSvg.Image.Quality |  |
| 235 | `Pat.Resolved.alignNone` | Pattern.lean:121 | 3 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 236 | `Pat.Resolved.contentSlot` | Pattern.lean:124 | 3 | frontx: unsupported parameter type LeanSvg.Pat.Resolved |  |
| 237 | `Pat.Rt.bicubic` | PatternRender.lean:78 | 3 | frontx: unsupported parameter type LeanSvg.Pat.Rt |  |
| 238 | `Poly.closed` | Geom.lean:159 | 3 | frontx: unsupported parameter type LeanSvg.Poly |  |
| 239 | `Render.Target.oy` | Render.lean:224 | 3 | frontx: unsupported parameter type LeanSvg.Render.Target |  |
| 240 | `Shape.Plan.globalMask` | Shape.lean:345 | 3 | frontx: unsupported parameter type LeanSvg.Shape.Plan |  |
| 241 | `Shape.Plan.gposScript` | Shape.lean:348 | 3 | frontx: unsupported parameter type LeanSvg.Shape.Plan |  |
| 242 | `Shape.instBEqSkip.beq` | Shape.lean:672 | 3 | frontx: unsupported parameter type LeanSvg.Shape.Skip |  |
| 243 | `Svg.ClipChild.fine` | Svg.lean:384 | 3 | frontx: unsupported parameter type LeanSvg.Svg.ClipChild |  |
| 244 | `Svg.ClipChild.visible` | Svg.lean:377 | 3 | frontx: unsupported parameter type LeanSvg.Svg.ClipChild |  |
| 245 | `Svg.Frame.isShapeLeaf` | Svg.lean:3725 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 246 | `Svg.Frame.maskUse` | Svg.lean:3711 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 247 | `Svg.Frame.mode` | Svg.lean:3701 | 3 | frontx: unsupported result type LeanSvg.Svg.ClipMode |  |
| 248 | `Svg.Frame.useSlot` | Svg.lean:3706 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 249 | `Svg.Frame.wantS` | Svg.lean:3737 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 250 | `Svg.Shape.markerable` | Svg.lean:315 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Shape |  |
| 251 | `Svg.Style.ctxStroke` | Svg.lean:271 | 3 | frontx: unsupported result type LeanSvg.Svg.Paint |  |
| 252 | `Svg.Style.fontAvailable` | Svg.lean:211 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 253 | `Svg.Style.fontItalic` | Svg.lean:174 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 254 | `Svg.Style.imageRendering` | Svg.lean:304 | 3 | frontx: unsupported result type LeanSvg.Image.Quality |  |
| 255 | `Svg.Style.markerCtx` | Svg.lean:283 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 256 | `Svg.Style.markersPos` | Svg.lean:100 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 257 | `Svg.Style.strokeFirst` | Svg.lean:97 | 3 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 258 | `Text.Cluster.base` | Text.lean:665 | 3 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 259 | `Text.SpanProps.anchor` | Text.lean:211 | 3 | frontx: unsupported result type LeanSvg.Text.Anchor |  |
| 260 | `Text.SpanProps.face` | Text.lean:192 | 3 | frontx: unsupported result type LeanSvg.Text.Face |  |
| 261 | `Text.SpanProps.lengthAdjustGlyphs` | Text.lean:244 | 3 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 262 | `Turbulence.Params.fractal` | Filter/Turbulence.lean:49 | 3 | frontx: unsupported parameter type LeanSvg.Turbulence.Params |  |
| 263 | `Units.Metrics.upem` | Units.lean:41 | 3 | frontx: unsupported parameter type LeanSvg.Units.Metrics |  |
| 264 | `Viewport.AspectRatio.slice` | Viewport.lean:29 | 3 | frontx: unsupported parameter type LeanSvg.Viewport.AspectRatio |  |
| 265 | `Pat.Rt.py` | PatternRender.lean:74 | 4 | frontx: unsupported result type LeanSvg.Grad.Axis |  |
| 266 | `Render.Layer.blend` | Render.lean:485 | 4 | frontx: unsupported result type LeanSvg.BlendMode |  |
| 267 | `Shape.Builder.stageSub` | Shape.lean:312 | 4 | frontx: unsupported parameter type LeanSvg.Shape.Builder |  |
| 268 | `Svg.Frame.ctxUse` | Svg.lean:3732 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 269 | `Svg.Frame.maskSlot` | Svg.lean:3714 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 270 | `Svg.GroupInfo.mask` | Svg.lean:471 | 4 | frontx: unsupported parameter type LeanSvg.Svg.GroupInfo |  |
| 271 | `Svg.MarkerEntry.orient` | Svg.lean:564 | 4 | frontx: unsupported result type LeanSvg.Svg.MarkerOrient |  |
| 272 | `Svg.Style.crisp` | Svg.lean:117 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 273 | `Svg.Style.ctxSlot` | Svg.lean:274 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 274 | `Svg.Style.fontFamily` | Svg.lean:214 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 275 | `Svg.Style.ownOpacity` | Svg.lean:103 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 276 | `Svg.Style.strokeCtx` | Svg.lean:279 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 277 | `Svg.Style.writingMode` | Svg.lean:201 | 4 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 278 | `Svg.rot90` | Svg.lean:1122 | 4 | frontx: unsupported result type LeanSvg.Svg.ArcDir |  |
| 279 | `Text.Cluster.dropped` | Text.lean:668 | 4 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 280 | `Text.Cluster.off` | Text.lean:672 | 4 | frontx: unsupported parameter type LeanSvg.Text.Cluster |  |
| 281 | `Text.SpanProps.bidiOverride` | Text.lean:251 | 4 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 282 | `Text.SpanProps.lang` | Text.lean:255 | 4 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 283 | `Text.SpanProps.rtl` | Text.lean:247 | 4 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 284 | `Text.SpanProps.throughIdx` | Text.lean:231 | 4 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 285 | `BasicShape.Spec.ref` | BasicShape.lean:76 | 5 | frontx: unsupported result type LeanSvg.BasicShape.RefBox |  |
| 286 | `Bidi.isIsoInit` | Bidi.lean:75 | 5 | frontx: unsupported parameter type LeanSvg.Bidi.Cls |  |
| 287 | `Bidi.isNI` | Bidi.lean:80 | 5 | frontx: unsupported parameter type LeanSvg.Bidi.Cls |  |
| 288 | `Grad.instBEqSpread.beq` | Shader.lean:331 | 5 | frontx: unsupported parameter type LeanSvg.Grad.Spread |  |
| 289 | `JpegDecode.Scan.al` | JpegDecode.lean:108 | 5 | frontx: unsupported parameter type LeanSvg.JpegDecode.Scan |  |
| 290 | `Lighting.Params.light` | Filter/Lighting.lean:51 | 5 | frontx: unsupported result type LeanSvg.Lighting.Light |  |
| 291 | `Pat.Rt.alpha8` | PatternRender.lean:81 | 5 | frontx: unsupported parameter type LeanSvg.Pat.Rt |  |
| 292 | `Render.Clip.y1` | Render.lean:64 | 5 | frontx: unsupported parameter type LeanSvg.Render.Clip |  |
| 293 | `Svg.Style.alignmentBaseline` | Svg.lean:206 | 5 | frontx: unsupported result type LeanSvg.Text.AlignmentBaseline |  |
| 294 | `Svg.Style.clipEvenOdd` | Svg.lean:249 | 5 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 295 | `Svg.Style.color` | Svg.lean:126 | 5 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 296 | `Svg.Style.opacity` | Svg.lean:92 | 5 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 297 | `Svg.Style.textCrisp` | Svg.lean:121 | 5 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 298 | `Text.SpanProps.alignmentBaseline` | Text.lean:215 | 5 | frontx: unsupported result type LeanSvg.Text.AlignmentBaseline |  |
| 299 | `Font.numGlyphs` | Font.lean:44 | 6 | frontx: unsupported parameter type LeanSvg.Font |  |
| 300 | `Options.background` | Render.lean:29 | 6 | frontx: unsupported parameter type LeanSvg.Options |  |
| 301 | `Shape.St.rtl` | Shape.lean:494 | 6 | frontx: unsupported parameter type LeanSvg.Shape.St |  |
| 302 | `Svg.Shape.style` | Svg.lean:309 | 6 | frontx: unsupported result type LeanSvg.Svg.Style |  |
| 303 | `Svg.Style.defs` | Svg.lean:150 | 6 | frontx: unsupported result type LeanSvg.Grad.Defs |  |
| 304 | `Svg.Style.ownLineThrough` | Svg.lean:232 | 6 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 305 | `Svg.Style.pctRefSet` | Svg.lean:131 | 6 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 306 | `Image.Rt.quality` | Image.lean:356 | 7 | frontx: unsupported result type LeanSvg.Image.Quality |  |
| 307 | `Svg.Frame.fine` | Svg.lean:3718 | 7 | frontx: unsupported parameter type LeanSvg.Svg.Frame |  |
| 308 | `Svg.GroupInfo.isolate` | Svg.lean:461 | 7 | frontx: unsupported parameter type LeanSvg.Svg.GroupInfo |  |
| 309 | `Svg.Style.visible` | Svg.lean:110 | 7 | frontx: unsupported parameter type LeanSvg.Svg.Style |  |
| 310 | `Text.SpanProps.baselineShiftSuper` | Text.lean:222 | 7 | frontx: unsupported parameter type LeanSvg.Text.SpanProps |  |
| 311 | `Font.tailLen` | Font.lean:111 | 8 | frontx: unsupported parameter type LeanSvg.Font |  |
| 312 | `Image.sniff` | Image.lean:210 | 8 | frontx: unsupported result type LeanSvg.Image.Fmt |  |
| 313 | `Text.ElemPos.hasRot` | Text.lean:268 | 8 | frontx: unsupported parameter type LeanSvg.Text.ElemPos |  |
| 314 | `Grad.RawStop.op` | Shader.lean:343 | 10 | frontx: unsupported parameter type LeanSvg.Grad.RawStop |  |
| 315 | `Svg.RootInfo.aspect` | Svg.lean:447 | 10 | frontx: unsupported result type LeanSvg.Viewport.AspectRatio |  |
| 316 | `Grad.Rt.isOpaque` | Shader.lean:688 | 11 | frontx: unsupported parameter type LeanSvg.Grad.Rt |  |
| 317 | `Grad.spreadT` | Shader.lean:825 | 11 | frontx: unsupported parameter type LeanSvg.Grad.Spread |  |
| 318 | `Image.fmtOf` | Image.lean:218 | 11 | frontx: unsupported result type LeanSvg.Image.Fmt |  |
| 319 | `Svg.Style.textAnchor` | Svg.lean:190 | 11 | frontx: unsupported result type LeanSvg.Text.Anchor |  |
| 320 | `Svg.GroupInfo.dropped` | Svg.lean:481 | 12 | frontx: unsupported parameter type LeanSvg.Svg.GroupInfo |  |
| 321 | `Text.matchWeight` | Text.lean:72 | 13 | frontx: unsupported parameter type List Nat |  |
| 322 | `FamilyMatch.matchStretch` | FamilyMatch.lean:118 | 14 | frontx: unsupported parameter type List Nat |  |
| 323 | `Text.pickFace` | Text.lean:85 | 15 | frontx: unsupported result type LeanSvg.Text.Face |  |
| 324 | `Options.threads` | Render.lean:42 | 18 | frontx: unsupported parameter type LeanSvg.Options |  |
| 325 | `Bidi.backScan` | Bidi.lean:477 | 22 | frontx: unsupported result type σ |  |
| 326 | `Svg.Shape.svgImage` | Svg.lean:321 | 50 | frontx: unsupported parameter type LeanSvg.Svg.Shape |  |
| 327 | `Bidi.levelCls` | Bidi.lean:85 | 191 | frontx: unsupported result type LeanSvg.Bidi.Cls |  |
| 328 | `FamilyMatch.fallbackOrder` | FamilyMatch.lean:153 | ? | frontx: unsupported result type List Nat |  |

### 1.3 Int / Fx scalar (also Int tuples, Option Int)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `BasicShape.Env.len` | BasicShape.lean:82 | 1 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 2 | `BasicShape.LP.abs` | BasicShape.lean:42 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 3 | `BasicShape.LP.pct` | BasicShape.lean:43 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 4 | `Box.x0` | Geom.lean:333 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 5 | `Box.x1` | Geom.lean:335 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 6 | `Box.y0` | Geom.lean:334 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 7 | `DSeg.p` | Geom.lean:845 | 1 | frontx: unsupported result type LeanSvg.Pt |  |
| 8 | `DSeg.q` | Geom.lean:846 | 1 | frontx: unsupported result type LeanSvg.Pt |  |
| 9 | `DSeg.tp` | Geom.lean:847 | 1 | frontx: unsupported result type LeanSvg.Pt |  |
| 10 | `FeImage.Job.sx` | Filter/ImageRender.lean:22 | 1 | frontx: unsupported result type Int |  |
| 11 | `FeImage.Job.uw` | Filter/ImageRender.lean:30 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 12 | `Filter.ElemCtx.vbW` | Filter.lean:864 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 13 | `Filter.URect.h` | Filter.lean:231 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 14 | `Filter.URect.w` | Filter.lean:230 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 15 | `Filter.URect.x` | Filter.lean:228 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 16 | `Filter.URect.y` | Filter.lean:229 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 17 | `FilterApply.Img.rh` | FilterApply.lean:111 | 1 | frontx: unsupported result type Int |  |
| 18 | `FilterApply.Img.rw` | FilterApply.lean:110 | 1 | frontx: unsupported result type Int |  |
| 19 | `FilterApply.Img.rx` | FilterApply.lean:108 | 1 | frontx: unsupported result type Int |  |
| 20 | `FilterApply.Img.ry` | FilterApply.lean:109 | 1 | frontx: unsupported result type Int |  |
| 21 | `FilterFrame.Back.k11` | FilterFrame.lean:36 | 1 | frontx: unsupported result type Int |  |
| 22 | `FilterFrame.Back.k12` | FilterFrame.lean:37 | 1 | frontx: unsupported result type Int |  |
| 23 | `FilterFrame.Back.k21` | FilterFrame.lean:38 | 1 | frontx: unsupported result type Int |  |
| 24 | `FilterFrame.Back.k22` | FilterFrame.lean:39 | 1 | frontx: unsupported result type Int |  |
| 25 | `FilterFrame.Back.tx` | FilterFrame.lean:40 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 26 | `FilterFrame.Back.ty` | FilterFrame.lean:41 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 27 | `FilterFrame.Back.vx` | FilterFrame.lean:47 | 1 | frontx: unsupported result type Int |  |
| 28 | `FilterFrame.Back.x0` | FilterFrame.lean:42 | 1 | frontx: unsupported result type Int |  |
| 29 | `FilterFrame.Plan.root` | FilterFrame.lean:58 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 30 | `Font.strikeoutPosition` | Font.lean:102 | 1 | frontx: unsupported result type Int |  |
| 31 | `ForeignObject.HStyle.lineHeight` | ForeignObject.lean:74 | 1 | frontx: unsupported result type Option (Bool × Int) |  |
| 32 | `ForeignObject.HStyle.size` | ForeignObject.lean:66 | 1 | frontx: unsupported result type Int |  |
| 33 | `Fx.abs` | Fixed.lean:41 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 34 | `Fx.ceil` | Fixed.lean:39 | 1 | frontx: unsupported result type Int |  |
| 35 | `Fx.floor` | Fixed.lean:38 | 1 | frontx: unsupported result type Int |  |
| 36 | `Fx.min` | Fixed.lean:42 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 37 | `Fx.round` | Fixed.lean:40 | 1 | frontx: unsupported result type Int |  |
| 38 | `Grad.Aff.a` | Shader.lean:183 | 1 | frontx: unsupported result type Int |  |
| 39 | `Grad.Aff.b` | Shader.lean:184 | 1 | frontx: unsupported result type Int |  |
| 40 | `Grad.Aff.c` | Shader.lean:185 | 1 | frontx: unsupported result type Int |  |
| 41 | `Grad.Aff.d` | Shader.lean:186 | 1 | frontx: unsupported result type Int |  |
| 42 | `Grad.Aff.e` | Shader.lean:187 | 1 | frontx: unsupported result type Int |  |
| 43 | `Grad.Axis.aH` | Shader.lean:657 | 1 | frontx: unsupported result type Int |  |
| 44 | `Grad.Axis.cH` | Shader.lean:658 | 1 | frontx: unsupported result type Int |  |
| 45 | `Grad.Axis.eH` | Shader.lean:659 | 1 | frontx: unsupported result type Int |  |
| 46 | `Grad.PctRef.w` | Shader.lean:506 | 1 | frontx: unsupported result type Int |  |
| 47 | `Grad.RawDef.transform` | Shader.lean:359 | 1 | frontx: unsupported result type Option LeanSvg.Mat |  |
| 48 | `Grad.RawStop.off` | Shader.lean:341 | 1 | frontx: unsupported result type Int |  |
| 49 | `Grad.Resolved.transform` | Shader.lean:408 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 50 | `Image.Placed.vh` | Image.lean:303 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 51 | `Image.Placed.vw` | Image.lean:302 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 52 | `Image.Placed.vx` | Image.lean:300 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 53 | `Image.Placed.vy` | Image.lean:301 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 54 | `Mat.a` | Geom.lean:62 | 1 | frontx: unsupported result type Int |  |
| 55 | `Mat.b` | Geom.lean:63 | 1 | frontx: unsupported result type Int |  |
| 56 | `Mat.c` | Geom.lean:64 | 1 | frontx: unsupported result type Int |  |
| 57 | `Mat.d` | Geom.lean:65 | 1 | frontx: unsupported result type Int |  |
| 58 | `Mat.e` | Geom.lean:66 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 59 | `Pat.Resolved.h` | Pattern.lean:116 | 1 | frontx: unsupported result type Int |  |
| 60 | `Pat.Resolved.transform` | Pattern.lean:112 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 61 | `Pat.Resolved.viewBox` | Pattern.lean:117 | 1 | frontx: unsupported result type Option (Int × Int × Int × Int) |  |
| 62 | `Pat.Resolved.w` | Pattern.lean:115 | 1 | frontx: unsupported result type Int |  |
| 63 | `Pat.Resolved.x` | Pattern.lean:113 | 1 | frontx: unsupported result type Int |  |
| 64 | `Pat.Resolved.y` | Pattern.lean:114 | 1 | frontx: unsupported result type Int |  |
| 65 | `Pt.x` | Geom.lean:13 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 66 | `Pt.y` | Geom.lean:14 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 67 | `Render.Clip.vx` | Render.lean:69 | 1 | frontx: unsupported result type Int |  |
| 68 | `Render.Layer.fts` | Render.lean:500 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 69 | `Render.Layer.lx` | Render.lean:505 | 1 | frontx: unsupported result type Int |  |
| 70 | `Render.Layer.root` | Render.lean:501 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 71 | `Shape.Glyph.xAdv` | ShapeRun.lean:1067 | 1 | frontx: unsupported result type Int |  |
| 72 | `Shape.Glyph.xOff` | ShapeRun.lean:1068 | 1 | frontx: unsupported result type Int |  |
| 73 | `StrokeStyle.width` | Geom.lean:487 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 74 | `Svg.ClipUse.ctm` | Svg.lean:423 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 75 | `Svg.CtxUse.ctm` | Svg.lean:411 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 76 | `Svg.MarkerEntry.height` | Svg.lean:554 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 77 | `Svg.MarkerEntry.refX` | Svg.lean:550 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 78 | `Svg.MarkerEntry.width` | Svg.lean:553 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 79 | `Svg.MaskEntry.pctH` | Svg.lean:515 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 80 | `Svg.MaskEntry.pctW` | Svg.lean:514 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 81 | `Svg.MaskUse.ctm` | Svg.lean:526 | 1 | frontx: unsupported result type LeanSvg.Mat |  |
| 82 | `Svg.RootInfo.height` | Svg.lean:444 | 1 | frontx: unsupported result type Option (LeanSvg.Fx × Bool) |  |
| 83 | `Svg.RootInfo.width` | Svg.lean:443 | 1 | frontx: unsupported result type Option (LeanSvg.Fx × Bool) |  |
| 84 | `Svg.Style.letterSpacing` | Svg.lean:180 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 85 | `Svg.Style.originDx` | Svg.lean:143 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 86 | `Svg.Style.ownTextLength` | Svg.lean:238 | 1 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 87 | `Svg.Style.pctRefW` | Svg.lean:137 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 88 | `Svg.Style.strokeWidth` | Svg.lean:81 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 89 | `SvgImage.Entry.w` | SvgImage.lean:82 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 90 | `SvgImage.Entry.x` | SvgImage.lean:80 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 91 | `SvgImage.Entry.y` | SvgImage.lean:81 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 92 | `Text.CharPos.dx` | Text.lean:428 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 93 | `Text.CharPos.dy` | Text.lean:429 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 94 | `Text.CharPos.x` | Text.lean:426 | 1 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 95 | `Text.CharPos.y` | Text.lean:427 | 1 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 96 | `Text.DecorRun.ox` | Text.lean:577 | 1 | frontx: unsupported result type Int |  |
| 97 | `Text.DecorRun.oy` | Text.lean:578 | 1 | frontx: unsupported result type Int |  |
| 98 | `Text.DecorRun.rot` | Text.lean:579 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 99 | `Text.DecorRun.width` | Text.lean:580 | 1 | frontx: unsupported result type Int |  |
| 100 | `Text.SpanProps.baselineShiftPx` | Text.lean:220 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 101 | `Text.SpanProps.letterSpacing` | Text.lean:207 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 102 | `Text.SpanProps.overlineSize` | Text.lean:236 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 103 | `Text.SpanProps.sizeAdjust` | Text.lean:206 | 1 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 104 | `Text.SpanProps.underlineSize` | Text.lean:235 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 105 | `TextPath.Cub.p0` | TextPath.lean:41 | 1 | frontx: unsupported result type Int × Int |  |
| 106 | `TextPath.Cub.p1` | TextPath.lean:42 | 1 | frontx: unsupported result type Int × Int |  |
| 107 | `TextPath.Cub.p2` | TextPath.lean:43 | 1 | frontx: unsupported result type Int × Int |  |
| 108 | `TextPath.Normal.cos` | TextPath.lean:229 | 1 | frontx: unsupported result type Int |  |
| 109 | `TextPath.Normal.x` | TextPath.lean:227 | 1 | frontx: unsupported result type Int |  |
| 110 | `TextPath.Normal.y` | TextPath.lean:228 | 1 | frontx: unsupported result type Int |  |
| 111 | `Turbulence.Params.seed` | Filter/Turbulence.lean:47 | 1 | frontx: unsupported result type Int |  |
| 112 | `Units.Metrics.cap` | Units.lean:48 | 1 | frontx: unsupported result type Int |  |
| 113 | `Units.Metrics.descent` | Units.lean:52 | 1 | frontx: unsupported result type Int |  |
| 114 | `Units.Metrics.xHeight` | Units.lean:49 | 1 | frontx: unsupported result type Int |  |
| 115 | `Units.RootLen.size` | Units.lean:34 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 116 | `Units.RootLen.vpW` | Units.lean:35 | 1 | frontx: unsupported result type LeanSvg.Fx |  |
| 117 | `BasicShape.LP.resolve` | BasicShape.lean:46 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 118 | `FeImage.Job.uh` | Filter/ImageRender.lean:31 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 119 | `Filter.ElemCtx.fontSize` | Filter.lean:862 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 120 | `FilterFrame.Back.fwd` | FilterFrame.lean:45 | 2 | frontx: unsupported result type LeanSvg.Mat |  |
| 121 | `FilterFrame.Back.y0` | FilterFrame.lean:43 | 2 | frontx: unsupported result type Int |  |
| 122 | `FilterFrame.Plan.fts` | FilterFrame.lean:56 | 2 | frontx: unsupported result type LeanSvg.Mat |  |
| 123 | `Font.descent` | Font.lean:53 | 2 | frontx: unsupported result type Int |  |
| 124 | `Font.superscriptOffset` | Font.lean:69 | 2 | frontx: unsupported result type Int |  |
| 125 | `Fx.mul` | Fixed.lean:36 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 126 | `Fx.ofNat` | Fixed.lean:34 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 127 | `Grad.PctRef.diag` | Shader.lean:510 | 2 | frontx: unsupported result type Int |  |
| 128 | `Options.zoom` | Render.lean:27 | 2 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 129 | `Svg.MarkerEntry.refY` | Svg.lean:551 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 130 | `Svg.RootInfo.viewBox` | Svg.lean:445 | 2 | frontx: unsupported result type Option (LeanSvg.Fx × LeanSvg.Fx × LeanSvg.Fx × LeanSvg.Fx) |  |
| 131 | `Svg.Style.miterLimit` | Svg.lean:84 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 132 | `SvgImage.Entry.h` | SvgImage.lean:83 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 133 | `Text.DecorRun.dyUnits` | Text.lean:587 | 2 | frontx: unsupported result type Int |  |
| 134 | `Text.SpanProps.wordSpacing` | Text.lean:208 | 2 | frontx: unsupported result type LeanSvg.Fx |  |
| 135 | `Units.Metrics.ascent` | Units.lean:50 | 2 | frontx: unsupported result type Int |  |
| 136 | `DSeg.tq` | Geom.lean:848 | 3 | frontx: unsupported result type LeanSvg.Pt |  |
| 137 | `Font.ascent` | Font.lean:50 | 3 | frontx: unsupported result type Int |  |
| 138 | `Font.capHeight` | Font.lean:63 | 3 | frontx: unsupported result type Int |  |
| 139 | `Font.subscriptOffset` | Font.lean:66 | 3 | frontx: unsupported result type Int |  |
| 140 | `Font.underlinePosition` | Font.lean:94 | 3 | frontx: unsupported result type Int |  |
| 141 | `Fx.clamp` | Fixed.lean:27 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 142 | `Fx.max` | Fixed.lean:43 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 143 | `Grad.Axis.split` | Shader.lean:665 | 3 | frontx: unsupported result type Int × Nat |  |
| 144 | `Grad.PctRef.h` | Shader.lean:507 | 3 | frontx: unsupported result type Int |  |
| 145 | `Mat.linInRange` | Geom.lean:81 | 3 | frontx: unsupported parameter type Int |  |
| 146 | `Pat.RawDef.transform` | Pattern.lean:72 | 3 | frontx: unsupported result type LeanSvg.Mat |  |
| 147 | `Render.Clip.vy` | Render.lean:70 | 3 | frontx: unsupported result type Int |  |
| 148 | `Render.Layer.ly` | Render.lean:506 | 3 | frontx: unsupported result type Int |  |
| 149 | `Shape.Glyph.yOff` | ShapeRun.lean:1069 | 3 | frontx: unsupported result type Int |  |
| 150 | `StrokeStyle.miterLimit` | Geom.lean:491 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 151 | `Svg.ClipChild.ctm` | Svg.lean:374 | 3 | frontx: unsupported result type LeanSvg.Mat |  |
| 152 | `Svg.ClipEntry.transform` | Svg.lean:390 | 3 | frontx: unsupported result type LeanSvg.Mat |  |
| 153 | `Svg.GroupInfo.filterCtm` | Svg.lean:476 | 3 | frontx: unsupported result type LeanSvg.Mat |  |
| 154 | `Svg.Style.fontSizeAdjust` | Svg.lean:184 | 3 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 155 | `Svg.Style.wordSpacing` | Svg.lean:181 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 156 | `SvgImage.Entry.inner` | SvgImage.lean:85 | 3 | frontx: unsupported result type LeanSvg.Mat |  |
| 157 | `Text.CharPos.rot` | Text.lean:430 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 158 | `Text.Cluster.adv` | Text.lean:650 | 3 | frontx: unsupported result type Int |  |
| 159 | `Text.Cluster.sx` | Text.lean:679 | 3 | frontx: unsupported result type Int |  |
| 160 | `Text.DecorRun.thicknessUnits` | Text.lean:589 | 3 | frontx: unsupported result type Int |  |
| 161 | `Text.SpanProps.size` | Text.lean:203 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 162 | `Text.SpanProps.textLength` | Text.lean:241 | 3 | frontx: unsupported result type Option LeanSvg.Fx |  |
| 163 | `TextPath.Normal.sin` | TextPath.lean:230 | 3 | frontx: unsupported result type Int |  |
| 164 | `TextPath.Seg.s0` | TextPath.lean:97 | 3 | frontx: unsupported result type Int |  |
| 165 | `TextPath.Table.total` | TextPath.lean:105 | 3 | frontx: unsupported result type Int |  |
| 166 | `TextPath.rdiv` | TextPath.lean:50 | 3 | frontx: unsupported result type Int |  |
| 167 | `Turbulence.trunc32` | Filter/Turbulence.lean:157 | 3 | frontx: unsupported result type Int |  |
| 168 | `Turbulence.wrap32` | Filter/Turbulence.lean:64 | 3 | frontx: unsupported result type Int |  |
| 169 | `Units.Metrics.lineGap` | Units.lean:53 | 3 | frontx: unsupported result type Int |  |
| 170 | `Use.resolveLen` | Use.lean:91 | 3 | frontx: unsupported result type LeanSvg.Fx |  |
| 171 | `FilterApply.scaleOf` | FilterApply.lean:467 | 4 | frontx: unsupported parameter type LeanSvg.Mat |  |
| 172 | `FilterFrame.Back.vy` | FilterFrame.lean:48 | 4 | frontx: unsupported result type Int |  |
| 173 | `Font.i8` | Font.lean:123 | 4 | frontx: unsupported result type Int |  |
| 174 | `Font.lineGap` | Font.lean:55 | 4 | frontx: unsupported result type Int |  |
| 175 | `Font.xHeight` | Font.lean:59 | 4 | frontx: unsupported result type Int |  |
| 176 | `Fx.hypot` | Fixed.lean:46 | 4 | frontx: unsupported result type LeanSvg.Fx |  |
| 177 | `Fx.inRange` | Fixed.lean:30 | 4 | frontx: unsupported parameter type LeanSvg.Fx |  |
| 178 | `Grad.norm2` | Shader.lean:152 | 4 | frontx: unsupported result type Int |  |
| 179 | `Grad.sqrt16` | Shader.lean:148 | 4 | frontx: unsupported result type Int |  |
| 180 | `Image.clampIx` | Image.lean:405 | 4 | frontx: unsupported parameter type Int |  |
| 181 | `Mat.clampLin` | Geom.lean:74 | 4 | frontx: unsupported result type Int |  |
| 182 | `Pat.RawDef.viewBox` | Pattern.lean:82 | 4 | frontx: unsupported result type Option (Int × Int × Int × Int) |  |
| 183 | `Raster.toFDot6` | Raster.lean:529 | 4 | frontx: unsupported result type Int |  |
| 184 | `ShapeText.SGlyph.width` | ShapeText.lean:47 | 4 | frontx: unsupported result type Int |  |
| 185 | `Svg.Mat.hasScale` | Svg.lean:2129 | 4 | frontx: unsupported parameter type LeanSvg.Mat |  |
| 186 | `Synth.skew` | Synth.lean:36 | 4 | frontx: unsupported result type Int × Int × Int × Int |  |
| 187 | `Text.Cluster.natWidth` | Text.lean:660 | 4 | frontx: unsupported result type Int |  |
| 188 | `Text.SpanProps.throughSize` | Text.lean:237 | 4 | frontx: unsupported result type LeanSvg.Fx |  |
| 189 | `Turbulence.sat32` | Filter/Turbulence.lean:60 | 4 | frontx: unsupported result type Int |  |
| 190 | `Units.RootLen.vpH` | Units.lean:36 | 4 | frontx: unsupported result type LeanSvg.Fx |  |
| 191 | `Box.y1` | Geom.lean:336 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 192 | `Filter.ElemCtx.vbH` | Filter.lean:865 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 193 | `Filter.mul16` | Filter.lean:466 | 5 | frontx: unsupported result type Int |  |
| 194 | `Font.roundDiv14` | Font.lean:131 | 5 | frontx: unsupported result type Int |  |
| 195 | `Font.underlineThickness` | Font.lean:97 | 5 | frontx: unsupported result type Int |  |
| 196 | `Fx.scale16` | Fixed.lean:50 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 197 | `Grad.Aff.f` | Shader.lean:188 | 5 | frontx: unsupported result type Int |  |
| 198 | `Grad.mul16` | Shader.lean:136 | 5 | frontx: unsupported result type Int |  |
| 199 | `Image.bicFar` | Image.lean:415 | 5 | frontx: unsupported result type Int |  |
| 200 | `Image.round32` | Image.lean:424 | 5 | frontx: unsupported parameter type Int |  |
| 201 | `Raster.insideW` | Raster.lean:83 | 5 | frontx: unsupported parameter type Int |  |
| 202 | `Render.Layer.maskMat` | Render.lean:493 | 5 | frontx: unsupported result type LeanSvg.Mat |  |
| 203 | `Svg.MarkerEntry.viewBox` | Svg.lean:555 | 5 | frontx: unsupported result type Option (LeanSvg.Fx × LeanSvg.Fx × LeanSvg.Fx × LeanSvg.Fx) |  |
| 204 | `Svg.Style.dashOffset` | Svg.lean:87 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 205 | `Svg.Style.ownMat` | Svg.lean:265 | 5 | frontx: unsupported result type LeanSvg.Mat |  |
| 206 | `Svg.Style.pctRefH` | Svg.lean:138 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 207 | `Text.DecorRun.size` | Text.lean:582 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 208 | `Text.Placed.boldSize` | Text.lean:298 | 5 | frontx: unsupported result type LeanSvg.Fx |  |
| 209 | `Text.roundDivI` | Text.lean:689 | 5 | frontx: unsupported result type Int |  |
| 210 | `Turbulence.random` | Filter/Turbulence.lean:94 | 5 | frontx: unsupported result type Int |  |
| 211 | `Woff.fitsI16` | Woff.lean:174 | 5 | frontx: unsupported parameter type Int |  |
| 212 | `arcSteps` | Geom.lean:532 | 5 | frontx: unsupported parameter type LeanSvg.Fx |  |
| 213 | `degToRad16` | Geom.lean:33 | 5 | frontx: unsupported result type Int |  |
| 214 | `BasicShape.sideDist` | BasicShape.lean:390 | 6 | frontx: unsupported result type LeanSvg.Fx |  |
| 215 | `Filter.n16At` | Filter.lean:421 | 6 | frontx: unsupported result type Option (Int × Nat) |  |
| 216 | `FilterApply.roundAwayDiv` | Filter/DisplacementMap.lean:30 | 6 | frontx: unsupported result type Int |  |
| 217 | `FilterApply.truncPx` | FilterApply.lean:471 | 6 | frontx: unsupported result type Int |  |
| 218 | `Image.bicNear` | Image.lean:409 | 6 | frontx: unsupported result type Int |  |
| 219 | `Raster.divRound` | Raster.lean:533 | 6 | frontx: unsupported result type Int |  |
| 220 | `Svg.Style.ctm` | Svg.lean:157 | 6 | frontx: unsupported result type LeanSvg.Mat |  |
| 221 | `Svg.Style.originDy` | Svg.lean:144 | 6 | frontx: unsupported result type LeanSvg.Fx |  |
| 222 | `Svg.viewportDiag` | Svg.lean:1786 | 6 | frontx: unsupported result type LeanSvg.Fx |  |
| 223 | `TextPath.Cub.p3` | TextPath.lean:44 | 6 | frontx: unsupported result type Int × Int |  |
| 224 | `cheapDistance` | Geom.lean:176 | 6 | frontx: unsupported result type LeanSvg.Fx |  |
| 225 | `FeImage.Job.sy` | Filter/ImageRender.lean:23 | 7 | frontx: unsupported result type Int |  |
| 226 | `Grad.div16` | Shader.lean:141 | 7 | frontx: unsupported result type Int |  |
| 227 | `Grad.hypot16` | Shader.lean:156 | 7 | frontx: unsupported parameter type Int |  |
| 228 | `Mask.Step.content` | Mask.lean:42 | 7 | frontx: unsupported result type LeanSvg.Mat |  |
| 229 | `Mat.f` | Geom.lean:67 | 7 | frontx: unsupported result type LeanSvg.Fx |  |
| 230 | `Options.viewport` | Render.lean:35 | 7 | frontx: unsupported result type Option (Int × Int × Nat × Nat) |  |
| 231 | `Svg.Style.fontSize` | Svg.lean:163 | 7 | frontx: unsupported result type LeanSvg.Fx |  |
| 232 | `Text.Cluster.width` | Text.lean:653 | 7 | frontx: unsupported result type Int |  |
| 233 | `TextPath.Cub.deriv` | TextPath.lean:65 | 8 | frontx: unsupported result type Int × Int |  |
| 234 | `TextPath.accuracyFor` | TextPath.lean:261 | 8 | frontx: unsupported result type Int |  |
| 235 | `TextPath.chord` | TextPath.lean:83 | 8 | frontx: unsupported result type Int |  |
| 236 | `Use.divRound` | Use.lean:94 | 8 | frontx: unsupported result type Int |  |
| 237 | `Marker.dirUnit16` | Marker.lean:86 | 9 | frontx: unsupported result type Int × Int |  |
| 238 | `Mask.coord` | Mask.lean:54 | 9 | frontx: unsupported result type Int |  |
| 239 | `Svg.hueRound` | Svg.lean:812 | 9 | frontx: unsupported result type Int |  |
| 240 | `Text.roundScale` | Text.lean:592 | 9 | frontx: unsupported result type Int |  |
| 241 | `TextPath.unit` | TextPath.lean:233 | 9 | frontx: unsupported result type Int × Int |  |
| 242 | `parseNumber` | Fixed.lean:141 | 9 | frontx: unsupported result type Option (LeanSvg.Fx × Nat) |  |
| 243 | `quadDeltaFromLine` | Geom.lean:229 | 9 | frontx: unsupported result type LeanSvg.Fx |  |
| 244 | `FilterFrame.invScaled` | FilterFrame.lean:62 | 10 | frontx: unsupported result type Option (Int × Int × Int × Int) |  |
| 245 | `Grad.cubicAt16` | Shader.lean:242 | 10 | frontx: unsupported result type LeanSvg.Fx |  |
| 246 | `signedArea2` | Geom.lean:516 | 10 | frontx: unsupported result type Int |  |
| 247 | `Filter.decTimes` | Filter.lean:586 | 11 | frontx: unsupported result type Int |  |
| 248 | `Pat.hairCoverage` | PatternRender.lean:208 | 11 | frontx: unsupported result type Option Int |  |
| 249 | `Svg.divRound` | Svg.lean:1111 | 11 | frontx: unsupported result type Int |  |
| 250 | `SvgImage.layerBox` | SvgImage.lean:118 | 11 | frontx: unsupported parameter type Int × Int × Int × Int |  |
| 251 | `Filter.expSmall` | Filter/Gamma.lean:51 | 12 | frontx: unsupported parameter type Int |  |
| 252 | `Filter.morphCeil` | Filter/Morphology.lean:104 | 12 | frontx: unsupported parameter type Int |  |
| 253 | `Filter.morphScaled` | Filter/Morphology.lean:37 | 12 | frontx: unsupported result type Int |  |
| 254 | `Pt.dist` | Geom.lean:21 | 12 | frontx: unsupported result type LeanSvg.Fx |  |
| 255 | `TextPath.Cub.eval` | TextPath.lean:53 | 12 | frontx: unsupported result type Int × Int |  |
| 256 | `len8` | Geom.lean:570 | 12 | frontx: unsupported result type LeanSvg.Fx |  |
| 257 | `FilterApply.stdDev` | FilterApply.lean:437 | 13 | frontx: unsupported parameter type Int |  |
| 258 | `Filter.morphDev` | Filter/Morphology.lean:116 | 14 | frontx: unsupported parameter type Int |  |
| 259 | `cubicDeltaFromLine` | Geom.lean:162 | 14 | frontx: unsupported result type LeanSvg.Fx |  |
| 260 | `scaleDecimal` | Fixed.lean:55 | 16 | frontx: unsupported parameter type Int |  |
| 261 | `Pat.conv` | Pattern.lean:206 | 18 | frontx: unsupported result type Int |  |
| 262 | `Turbulence.r64` | Filter/Turbulence.lean:139 | 18 | frontx: unsupported result type Int × Nat |  |
| 263 | `parseNumber16` | Fixed.lean:150 | 18 | frontx: unsupported result type Option (Int × Nat) |  |
| 264 | `Grad.clampTo` | Shader.lean:163 | 19 | frontx: unsupported result type Int |  |
| 265 | `Filter.lnBig` | Filter/Gamma.lean:31 | 20 | frontx: unsupported result type Int |  |
| 266 | `Woff.triplet` | Woff.lean:154 | 20 | frontx: unsupported result type Int × Int × Nat |  |
| 267 | `strokeReach` | Geom.lean:494 | 22 | frontx: unsupported result type LeanSvg.Fx |  |
| 268 | `sinCos16` | Geom.lean:38 | 23 | frontx: unsupported result type Int × Int |  |
| 269 | `Text.rotMat16` | Text.lean:512 | 24 | frontx: unsupported result type Int × Int × Int × Int |  |
| 270 | `joinSteps` | Geom.lean:537 | 25 | frontx: unsupported parameter type LeanSvg.Fx |  |
| 271 | `Pat.roundDiv` | Pattern.lean:180 | 26 | frontx: unsupported result type Int |  |
| 272 | `Raster.mkEdgeCrisp` | Raster.lean:337 | 27 | frontx: unsupported result type Option (Int × Int × Nat × Nat × Int) |  |
| 273 | `Raster.mkEdge` | Raster.lean:117 | 30 | frontx: unsupported result type Option (Int × Int × Nat × Nat × Int) |  |
| 274 | `Render.hairCoverage` | Render.lean:189 | 30 | frontx: unsupported result type Option Int |  |
| 275 | `Font.unitsToFx16` | Font.lean:136 | 32 | frontx: unsupported result type Int |  |
| 276 | `Svg.hslToRgb` | Svg.lean:852 | 34 | frontx: unsupported parameter type Int |  |
| 277 | `Grad.Aff.invert` | Shader.lean:206 | 36 | frontx: unsupported result type Option (Int × Int × Int × Int × Int × Int) |  |
| 278 | `parseDecimal` | Fixed.lean:71 | 70 | frontx: unsupported result type Option (Bool × Nat × Int × Nat) |  |
| 279 | `Synth.boldWidth` | Synth.lean:40 | ? | frontx: unsupported result type LeanSvg.Fx |  |

### 1.4 Array (of scalars, tuples or structures) as value

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Brotli.Code.count` | Brotli.lean:64 | 1 | frontx: unsupported result type Array Nat |  |
| 2 | `Css.Decl.value` | Css.lean:88 | 1 | frontx: unsupported result type ByteArray |  |
| 3 | `Css.Rule.decls` | Css.lean:94 | 1 | frontx: unsupported result type Array LeanSvg.Css.Decl |  |
| 4 | `Css.Selector.components` | Css.lean:82 | 1 | frontx: unsupported result type Array LeanSvg.Css.Component |  |
| 5 | `Filter.RawFilter.attrs` | Filter.lean:290 | 1 | frontx: unsupported result type Array LeanSvg.Xml.Attr |  |
| 6 | `Filter.RawPrim.attrs` | Filter.lean:277 | 1 | frontx: unsupported result type Array LeanSvg.Xml.Attr |  |
| 7 | `Filter.RawPrim.floodColor` | Filter.lean:283 | 1 | frontx: unsupported result type Option ByteArray |  |
| 8 | `Filter.RawPrim.floodOpacity` | Filter.lean:284 | 1 | frontx: unsupported result type Option ByteArray |  |
| 9 | `Filter.Table.filters` | Filter.lean:297 | 1 | frontx: unsupported result type Array LeanSvg.Filter.RawFilter |  |
| 10 | `FontFace.Face.family` | FontFace.lean:47 | 1 | frontx: unsupported result type ByteArray |  |
| 11 | `ForeignObject.Line.pieces` | ForeignObject.lean:253 | 1 | frontx: unsupported result type Array (ByteArray × LeanSvg.ForeignObject.HStyle) |  |
| 12 | `Jpeg.Huff.offset` | Jpeg/Huffman.lean:48 | 1 | frontx: unsupported result type Array Int |  |
| 13 | `JpegDecode.Frame.comps` | JpegDecode.lean:96 | 1 | frontx: unsupported result type Array LeanSvg.JpegDecode.Comp |  |
| 14 | `JpegDecode.Scan.comps` | JpegDecode.lean:104 | 1 | frontx: unsupported result type Array (Nat × Nat × Nat) |  |
| 15 | `Pat.Defs.buckets` | Pattern.lean:129 | 1 | frontx: unsupported result type Array (Array Nat) |  |
| 16 | `Pat.Defs.defs` | Pattern.lean:128 | 1 | frontx: unsupported result type Array LeanSvg.Pat.Resolved |  |
| 17 | `PngDecode.Meta.plte` | PngDecode.lean:72 | 1 | frontx: unsupported result type Option ByteArray |  |
| 18 | `Poly.pts` | Geom.lean:158 | 1 | frontx: unsupported result type Array LeanSvg.Pt |  |
| 19 | `Render.Layer.masks` | Render.lean:492 | 1 | frontx: unsupported result type Array LeanSvg.Mask.Step |  |
| 20 | `Shape.Builder.feats` | Shape.lean:310 | 1 | frontx: unsupported result type Array LeanSvg.Shape.FeatureInfo |  |
| 21 | `Shape.Builder.pauses` | Shape.lean:311 | 1 | frontx: unsupported result type Array LeanSvg.Shape.Pause |  |
| 22 | `Shape.Plan.gsub` | Shape.lean:341 | 1 | frontx: unsupported result type Array (Array LeanSvg.Shape.LookupMap × LeanSvg.Shape.Pause |  |
| 23 | `Shape.Plan.masks` | Shape.lean:344 | 1 | frontx: unsupported result type Array (Nat × Nat × Nat) |  |
| 24 | `Shape.Rule.ahead` | Shape.lean:947 | 1 | frontx: unsupported result type Array Nat |  |
| 25 | `Shape.Rule.back` | Shape.lean:945 | 1 | frontx: unsupported result type Array Nat |  |
| 26 | `Shape.Rule.input` | Shape.lean:946 | 1 | frontx: unsupported result type Array Nat |  |
| 27 | `Shape.St.info` | Shape.lean:477 | 1 | frontx: unsupported result type Array LeanSvg.Shape.GInfo |  |
| 28 | `Shape.St.out` | Shape.lean:478 | 1 | frontx: unsupported result type Array LeanSvg.Shape.GInfo |  |
| 29 | `Shape.St.pos` | Shape.lean:479 | 1 | frontx: unsupported result type Array LeanSvg.Shape.GPos |  |
| 30 | `Svg.ClipChild.cmds` | Svg.lean:372 | 1 | frontx: unsupported result type Array LeanSvg.PathCmd |  |
| 31 | `Svg.Doc.clips` | Svg.lean:602 | 1 | frontx: unsupported result type Array LeanSvg.Svg.ClipEntry |  |
| 32 | `Svg.Doc.masks` | Svg.lean:605 | 1 | frontx: unsupported result type Array LeanSvg.Svg.MaskEntry |  |
| 33 | `Svg.GroupInfo.filters` | Svg.lean:475 | 1 | frontx: unsupported result type Array LeanSvg.Filter.Resolved |  |
| 34 | `Svg.MaskEntry.nodes` | Svg.lean:518 | 1 | frontx: unsupported result type Array LeanSvg.Svg.Node |  |
| 35 | `Svg.Shape.cmds` | Svg.lean:308 | 1 | frontx: unsupported result type Array LeanSvg.PathCmd |  |
| 36 | `Svg.Style.dashes` | Svg.lean:86 | 1 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 37 | `Text.ElemPos.dxs` | Text.lean:262 | 1 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 38 | `Text.ElemPos.dys` | Text.lean:263 | 1 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 39 | `Text.ElemPos.xs` | Text.lean:260 | 1 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 40 | `Text.ElemPos.ys` | Text.lean:261 | 1 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 41 | `Text.dropFirst` | Text.lean:355 | 1 | frontx: unsupported result type Array Nat |  |
| 42 | `Text.dropLast` | Text.lean:356 | 1 | frontx: unsupported result type Array Nat |  |
| 43 | `Text.firstIs` | Text.lean:357 | 1 | frontx: unsupported parameter type Array Nat |  |
| 44 | `Text.lastIs` | Text.lean:358 | 1 | frontx: unsupported parameter type Array Nat |  |
| 45 | `TextPath.Seg.pts` | TextPath.lean:94 | 1 | frontx: unsupported result type Array (Int × Int) |  |
| 46 | `Turbulence.Axis.b0` | Filter/Turbulence.lean:192 | 1 | frontx: unsupported result type Array Nat |  |
| 47 | `Turbulence.Axis.b1` | Filter/Turbulence.lean:193 | 1 | frontx: unsupported result type Array Nat |  |
| 48 | `Turbulence.Axis.r0` | Filter/Turbulence.lean:194 | 1 | frontx: unsupported result type Array Int64 |  |
| 49 | `Use.St.out` | Use.lean:172 | 1 | frontx: unsupported result type Array LeanSvg.Xml.Event |  |
| 50 | `Filter.RawFilter.prims` | Filter.lean:291 | 2 | frontx: unsupported result type Array LeanSvg.Filter.RawPrim |  |
| 51 | `ForeignObject.HStyle.color` | ForeignObject.lean:64 | 2 | frontx: unsupported result type ByteArray |  |
| 52 | `ForeignObject.HStyle.family` | ForeignObject.lean:69 | 2 | frontx: unsupported result type ByteArray |  |
| 53 | `Grad.Defs.buckets` | Shader.lean:420 | 2 | frontx: unsupported result type Array (Array Nat) |  |
| 54 | `Inflate.Huff.tab` | Inflate.lean:37 | 2 | frontx: unsupported result type Array Nat |  |
| 55 | `Jpeg.Huff.maxcode` | Jpeg/Huffman.lean:46 | 2 | frontx: unsupported result type Array Int |  |
| 56 | `Jpeg.Huff.vals` | Jpeg/Huffman.lean:49 | 2 | frontx: unsupported result type ByteArray |  |
| 57 | `PngDecode.Meta.trns` | PngDecode.lean:73 | 2 | frontx: unsupported result type Option ByteArray |  |
| 58 | `Render.Layer.filters` | Render.lean:498 | 2 | frontx: unsupported result type Array LeanSvg.Filter.Resolved |  |
| 59 | `Shape.Plan.gpos` | Shape.lean:342 | 2 | frontx: unsupported result type Array LeanSvg.Shape.LookupMap |  |
| 60 | `Shape.Rule.records` | Shape.lean:948 | 2 | frontx: unsupported result type Array (Nat × Nat) |  |
| 61 | `Svg.Doc.ctxUses` | Svg.lean:623 | 2 | frontx: unsupported result type Array LeanSvg.Svg.CtxUse |  |
| 62 | `Svg.Doc.nodes` | Svg.lean:600 | 2 | frontx: unsupported result type Array LeanSvg.Svg.Node |  |
| 63 | `Svg.Doc.patternContent` | Svg.lean:619 | 2 | frontx: unsupported result type Array (Array LeanSvg.Svg.Node) |  |
| 64 | `Svg.Doc.svgImages` | Svg.lean:621 | 2 | frontx: unsupported result type Array LeanSvg.SvgImage.Entry |  |
| 65 | `Svg.Doc.uses` | Svg.lean:603 | 2 | frontx: unsupported result type Array LeanSvg.Svg.ClipUse |  |
| 66 | `Svg.SpanLayers.owners` | Svg.lean:3199 | 2 | frontx: unsupported result type Array (LeanSvg.Svg.Style × Option LeanSvg.Box) |  |
| 67 | `Svg.Style.arcJoins` | Svg.lean:187 | 2 | frontx: unsupported result type Array Nat |  |
| 68 | `TextPath.Seg.cum` | TextPath.lean:95 | 2 | frontx: unsupported result type Array Int |  |
| 69 | `TextPath.Table.segs` | TextPath.lean:103 | 2 | frontx: unsupported result type Array LeanSvg.TextPath.Seg |  |
| 70 | `Turbulence.Axis.s` | Filter/Turbulence.lean:195 | 2 | frontx: unsupported result type Array Int64 |  |
| 71 | `Xml.Scoped.attrs` | Xml.lean:91 | 2 | frontx: unsupported result type Array LeanSvg.Xml.Attr |  |
| 72 | `Brotli.Code.syms` | Brotli.lean:65 | 3 | frontx: unsupported result type Array Nat |  |
| 73 | `Clip.Mask.m` | Clip.lean:91 | 3 | frontx: unsupported result type Array Nat |  |
| 74 | `Font.gposKernSubtables` | Font.lean:91 | 3 | frontx: unsupported result type Array Nat |  |
| 75 | `Image.Pix.px` | Image.lean:232 | 3 | frontx: unsupported result type Array Nat |  |
| 76 | `Jpeg.Huff.lookup` | Jpeg/Huffman.lean:43 | 3 | frontx: unsupported result type Array Nat |  |
| 77 | `Render.Layer.clips` | Render.lean:489 | 3 | frontx: unsupported result type Array LeanSvg.Clip.Mask |  |
| 78 | `Shape.St.matchPos` | Shape.lean:491 | 3 | frontx: unsupported result type Array Nat |  |
| 79 | `Svg.ClipEntry.children` | Svg.lean:401 | 3 | frontx: unsupported result type Array LeanSvg.Svg.ClipChild |  |
| 80 | `Svg.DefsScan.patterns` | Svg.lean:2875 | 3 | frontx: unsupported result type Array LeanSvg.Pat.RawDef |  |
| 81 | `Svg.Doc.markers` | Svg.lean:610 | 3 | frontx: unsupported result type Array LeanSvg.Svg.MarkerEntry |  |
| 82 | `Svg.GroupInfo.clips` | Svg.lean:468 | 3 | frontx: unsupported result type Array Nat |  |
| 83 | `Svg.SpanLayers.chains` | Svg.lean:3201 | 3 | frontx: unsupported result type Array (Array Nat) |  |
| 84 | `Svg.Style.clipShapeRaw` | Svg.lean:258 | 3 | frontx: unsupported result type Option ByteArray |  |
| 85 | `SvgImage.Entry.events` | SvgImage.lean:75 | 3 | frontx: unsupported result type Array LeanSvg.Xml.Event |  |
| 86 | `Text.Cluster.glyphs` | Text.lean:676 | 3 | frontx: unsupported result type Array (Nat × Nat × Int × Int) |  |
| 87 | `Text.Placed.cmds` | Text.lean:295 | 3 | frontx: unsupported result type Array LeanSvg.PathCmd |  |
| 88 | `Woff.pushU16` | Woff.lean:53 | 3 | frontx: unsupported result type ByteArray |  |
| 89 | `Woff.pushU32` | Woff.lean:56 | 3 | frontx: unsupported result type ByteArray |  |
| 90 | `BasicShape.Env.pathData` | BasicShape.lean:83 | 4 | frontx: unsupported result type Array LeanSvg.PathCmd |  |
| 91 | `Brotli.setByte` | Brotli.lean:312 | 4 | frontx: unsupported result type ByteArray |  |
| 92 | `FeImage.cost` | Filter/ImageRender.lean:65 | 4 | frontx: unsupported parameter type Array LeanSvg.Xml.Event |  |
| 93 | `Grad.Defs.defs` | Shader.lean:416 | 4 | frontx: unsupported result type Array LeanSvg.Grad.Resolved |  |
| 94 | `Grad.Rt.stops` | Shader.lean:684 | 4 | frontx: unsupported result type Array LeanSvg.Grad.RtStop |  |
| 95 | `Png.be32` | Png.lean:154 | 4 | frontx: unsupported result type ByteArray |  |
| 96 | `PngDecode.Fmt.pal` | PngDecode.lean:181 | 4 | frontx: unsupported result type ByteArray |  |
| 97 | `Svg.ClipChild.clips` | Svg.lean:380 | 4 | frontx: unsupported result type Array Nat |  |
| 98 | `Svg.Doc.maskUses` | Svg.lean:606 | 4 | frontx: unsupported result type Array LeanSvg.Svg.MaskUse |  |
| 99 | `Svg.MarkerEntry.content` | Svg.lean:587 | 4 | frontx: unsupported result type Array LeanSvg.Svg.Node |  |
| 100 | `Svg.Style.clips` | Svg.lean:261 | 4 | frontx: unsupported result type Array Nat |  |
| 101 | `Svg.Style.fontFamilyRaw` | Svg.lean:218 | 4 | frontx: unsupported result type ByteArray |  |
| 102 | `Svg.paintOrderPos` | Svg.lean:2051 | 4 | frontx: unsupported parameter type Array Nat |  |
| 103 | `Text.ElemPos.rots` | Text.lean:264 | 4 | frontx: unsupported result type Array LeanSvg.Fx |  |
| 104 | `Text.allSpace` | Text.lean:359 | 4 | frontx: unsupported parameter type Array Nat |  |
| 105 | `Woff.pushI16` | Woff.lean:59 | 4 | frontx: unsupported result type ByteArray |  |
| 106 | `Xml.Attr.value` | Xml.lean:38 | 4 | frontx: unsupported result type ByteArray |  |
| 107 | `Canvas.px` | Canvas.lean:26 | 5 | frontx: unsupported result type Array Nat |  |
| 108 | `Grad.Resolved.stops` | Shader.lean:410 | 5 | frontx: unsupported result type Array LeanSvg.Grad.RawStop |  |
| 109 | `Grad.Rt.ramp` | Shader.lean:699 | 5 | frontx: unsupported result type Array Nat |  |
| 110 | `Svg.DefsScan.grads` | Svg.lean:2861 | 5 | frontx: unsupported result type Array LeanSvg.Grad.RawDef |  |
| 111 | `Svg.Doc.events` | Svg.lean:613 | 5 | frontx: unsupported result type Array LeanSvg.Xml.Event |  |
| 112 | `Svg.Style.filterRaw` | Svg.lean:294 | 5 | frontx: unsupported result type Option ByteArray |  |
| 113 | `dropClosingDup` | Geom.lean:727 | 5 | frontx: unsupported result type Array LeanSvg.Pt |  |
| 114 | `Font.data` | Font.lean:103 | 6 | frontx: unsupported result type ByteArray |  |
| 115 | `PngDecode.passes` | PngDecode.lean:122 | 6 | frontx: unsupported result type Array (Nat × Nat × Nat × Nat) |  |
| 116 | `Raster.addAlpha` | Raster.lean:88 | 6 | frontx: unsupported result type Array Nat |  |
| 117 | `Woff.pad4` | Woff.lean:63 | 6 | frontx: unsupported result type ByteArray |  |
| 118 | `Bytes.lower` | Bytes.lean:88 | 7 | frontx: unsupported result type ByteArray |  |
| 119 | `FontFace.Face.coverage` | FontFace.lean:51 | 7 | frontx: unsupported result type Array (Nat × Nat) |  |
| 120 | `FontFace.addCp` | FontFace.lean:68 | 7 | frontx: unsupported result type Array (Nat × Nat) |  |
| 121 | `GifDecode.initDict` | GifDecode.lean:81 | 7 | frontx: unsupported result type Array (Array Nat) |  |
| 122 | `Inflate.copyBack` | Inflate.lean:110 | 7 | frontx: unsupported result type ByteArray |  |
| 123 | `Svg.padChains` | Svg.lean:3217 | 7 | frontx: unsupported result type Array (Array Nat) |  |
| 124 | `Svg.stripFragmentId` | Svg.lean:3152 | 7 | frontx: unsupported result type Option ByteArray |  |
| 125 | `pushRing` | Geom.lean:604 | 7 | frontx: unsupported result type Array (Array LeanSvg.Pt) |  |
| 126 | `Svg.Style.docFaces` | Svg.lean:222 | 8 | frontx: unsupported result type Array LeanSvg.FontFace.Face |  |
| 127 | `Png.blockHeader` | Png.lean:171 | 9 | frontx: unsupported result type ByteArray |  |
| 128 | `Png.crcAdvance` | Png.lean:34 | 9 | frontx: unsupported result type Array UInt32 |  |
| 129 | `ShapeText.byteOffsets` | ShapeText.lean:65 | 9 | frontx: unsupported result type Array Nat |  |
| 130 | `StixNonUnicode.utf8` | StixNonUnicode.lean:25 | 9 | frontx: unsupported result type Array UInt8 |  |
| 131 | `FontFace.stripQuotes` | FontFace.lean:58 | 10 | frontx: unsupported result type ByteArray |  |
| 132 | `GifDecode.pushGifPx` | GifDecode.lean:159 | 10 | frontx: unsupported result type ByteArray |  |
| 133 | `Inflate.stored` | Inflate.lean:182 | 10 | frontx: unsupported result type Option (Nat × ByteArray) |  |
| 134 | `ShapeText.charOf` | ShapeText.lean:74 | 10 | frontx: unsupported parameter type Array Nat |  |
| 135 | `Brotli.upperAt` | Brotli.lean:316 | 11 | frontx: unsupported result type ByteArray × Nat |  |
| 136 | `Image.trimBy` | Image.lean:142 | 11 | frontx: unsupported result type ByteArray |  |
| 137 | `Png.storedRows` | Png.lean:195 | 11 | frontx: unsupported result type ByteArray |  |
| 138 | `GifDecode.subBlocks` | GifDecode.lean:45 | 12 | frontx: unsupported result type Option (Nat × ByteArray) |  |
| 139 | `Raster.Mask.cov` | Raster.lean:71 | 12 | frontx: unsupported result type Array Nat |  |
| 140 | `BasicShape.words` | BasicShape.lean:93 | 13 | frontx: unsupported result type Array ByteArray |  |
| 141 | `GifDecode.rowOrder` | GifDecode.lean:146 | 13 | frontx: unsupported result type Array Nat |  |
| 142 | `FilterApply.boxSizes` | FilterApply.lean:362 | 14 | frontx: unsupported result type Array Nat |  |
| 143 | `Text.trimChars` | Text.lean:341 | 14 | frontx: unsupported result type Array Nat |  |
| 144 | `Png.storedPieces` | Png.lean:180 | 15 | frontx: unsupported result type ByteArray × Nat |  |
| 145 | `PngDecode.palette` | PngDecode.lean:200 | 15 | frontx: unsupported result type ByteArray |  |
| 146 | `PngDecode.trnsKey` | PngDecode.lean:185 | 15 | frontx: unsupported parameter type Option ByteArray |  |
| 147 | `dashPattern` | Geom.lean:892 | 16 | frontx: unsupported result type Option (Array LeanSvg.Fx × LeanSvg.Fx) |  |
| 148 | `Svg.stripQuotes` | Svg.lean:1851 | 17 | frontx: unsupported result type ByteArray |  |
| 149 | `Raster.hairPx` | Raster.lean:539 | 18 | frontx: unsupported result type Array Nat |  |
| 150 | `FontFace.splitTop` | FontFace.lean:178 | 19 | frontx: unsupported result type Array ByteArray |  |
| 151 | `ForeignObject.tokens` | ForeignObject.lean:233 | 19 | frontx: unsupported result type Array (Option ByteArray) |  |
| 152 | `Turbulence.noise` | Filter/Turbulence.lean:226 | 19 | frontx: unsupported parameter type Array Int64 |  |
| 153 | `Brotli.runningSums` | Brotli.lean:350 | 21 | frontx: unsupported result type Array Nat |  |
| 154 | `FontFace.base64` | FontFace.lean:116 | 22 | frontx: unsupported result type Option ByteArray |  |
| 155 | `Brotli.transformWord` | Brotli.lean:327 | 23 | frontx: unsupported result type ByteArray |  |
| 156 | `Raster.blitSpan` | Raster.lean:94 | 23 | frontx: unsupported result type Array Nat |  |
| 157 | `Grad.RawDef.stops` | Shader.lean:374 | 25 | frontx: unsupported result type Array LeanSvg.Grad.RawStop |  |
| 158 | `Filter.Resolved.prims` | Filter.lean:249 | 26 | frontx: unsupported result type Array LeanSvg.Filter.Prim |  |
| 159 | `Text.decodeUtf8` | Text.lean:303 | 38 | frontx: unsupported result type Array Nat |  |
| 160 | `ImageData.Decoded.px` | ImageData.lean:22 | ? | frontx: unsupported result type ByteArray |  |

### 1.5 recursion shape

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Grad.RtStop.b` | Shader.lean:621 | 1 | frontx: recursive call not in tail position self.b |  |
| 2 | `Grad.RtStop.g` | Shader.lean:620 | 1 | frontx: recursive call not in tail position self.g |  |
| 3 | `Grad.RtStop.off` | Shader.lean:618 | 1 | frontx: recursive call not in tail position self.off |  |
| 4 | `Grad.RtStop.r` | Shader.lean:619 | 1 | frontx: recursive call not in tail position self.r |  |
| 5 | `ImageData.Decoded.h` | ImageData.lean:21 | 1 | frontx: recursive call not in tail position self.h |  |
| 6 | `ImageData.Decoded.w` | ImageData.lean:20 | 1 | frontx: recursive call not in tail position self.w |  |
| 7 | `JpegDecode.Comp.bw` | JpegDecode.lean:89 | 1 | frontx: recursive call not in tail position self.bw |  |
| 8 | `JpegDecode.Comp.h` | JpegDecode.lean:85 | 1 | frontx: recursive call not in tail position self.h |  |
| 9 | `JpegDecode.Comp.id` | JpegDecode.lean:84 | 1 | frontx: recursive call not in tail position self.id |  |
| 10 | `JpegDecode.Comp.v` | JpegDecode.lean:86 | 1 | frontx: recursive call not in tail position self.v |  |
| 11 | `Lighting.V3.x` | Filter/Lighting.lean:190 | 1 | frontx: recursive call not in tail position self.x |  |
| 12 | `Lighting.V3.y` | Filter/Lighting.lean:191 | 1 | frontx: recursive call not in tail position self.y |  |
| 13 | `PngDecode.Fmt.ctype` | PngDecode.lean:178 | 1 | frontx: recursive call not in tail position self.ctype |  |
| 14 | `PngDecode.Fmt.depth` | PngDecode.lean:179 | 1 | frontx: recursive call not in tail position self.depth |  |
| 15 | `PngDecode.Fmt.key` | PngDecode.lean:180 | 1 | frontx: recursive call not in tail position self.key |  |
| 16 | `PngDecode.Hdr.ctype` | PngDecode.lean:47 | 1 | frontx: recursive call not in tail position self.ctype |  |
| 17 | `PngDecode.Hdr.depth` | PngDecode.lean:46 | 1 | frontx: recursive call not in tail position self.depth |  |
| 18 | `PngDecode.Hdr.h` | PngDecode.lean:45 | 1 | frontx: recursive call not in tail position self.h |  |
| 19 | `PngDecode.Hdr.w` | PngDecode.lean:44 | 1 | frontx: recursive call not in tail position self.w |  |
| 20 | `Rgba.a` | Canvas.lean:20 | 1 | frontx: recursive call not in tail position self.a |  |
| 21 | `Rgba.b` | Canvas.lean:19 | 1 | frontx: recursive call not in tail position self.b |  |
| 22 | `Rgba.g` | Canvas.lean:18 | 1 | frontx: recursive call not in tail position self.g |  |
| 23 | `Rgba.r` | Canvas.lean:17 | 1 | frontx: recursive call not in tail position self.r |  |
| 24 | `Shape.FeatureInfo.flags` | Shape.lean:303 | 1 | frontx: recursive call not in tail position self.flags |  |
| 25 | `Shape.FeatureInfo.maxValue` | Shape.lean:302 | 1 | frontx: recursive call not in tail position self.maxValue |  |
| 26 | `Shape.FeatureInfo.seq` | Shape.lean:301 | 1 | frontx: recursive call not in tail position self.seq |  |
| 27 | `Shape.FeatureInfo.stageSub` | Shape.lean:304 | 1 | frontx: recursive call not in tail position self.stageSub |  |
| 28 | `Shape.FeatureInfo.tag` | Shape.lean:300 | 1 | frontx: recursive call not in tail position self.tag |  |
| 29 | `Shape.GInfo.cluster` | Shape.lean:70 | 1 | frontx: recursive call not in tail position self.cluster |  |
| 30 | `Shape.GInfo.lig` | Shape.lean:84 | 1 | frontx: recursive call not in tail position self.lig |  |
| 31 | `Svg.SubCfg.layerDepth` | Svg.lean:3882 | 1 | frontx: recursive call not in tail position self.layerDepth |  |
| 32 | `JpegDecode.Comp.bh` | JpegDecode.lean:90 | 2 | frontx: recursive call not in tail position self.bh |  |
| 33 | `JpegDecode.Comp.tq` | JpegDecode.lean:87 | 2 | frontx: recursive call not in tail position self.tq |  |
| 34 | `PngDecode.Hdr.interlace` | PngDecode.lean:48 | 2 | frontx: recursive call not in tail position (accumulator mode needs a `Nat` result) |  |
| 35 | `Shape.GInfo.cat` | Shape.lean:87 | 2 | frontx: recursive call not in tail position self.cat |  |
| 36 | `Shape.GInfo.cp` | Shape.lean:66 | 2 | frontx: recursive call not in tail position self.cp |  |
| 37 | `Shape.GInfo.gc` | Shape.lean:74 | 2 | frontx: recursive call not in tail position self.gc |  |
| 38 | `Shape.GInfo.gid` | Shape.lean:68 | 2 | frontx: recursive call not in tail position self.gid |  |
| 39 | `Shape.GInfo.gprops` | Shape.lean:82 | 2 | frontx: recursive call not in tail position self.gprops |  |
| 40 | `Grad.RtStop.a` | Shader.lean:622 | 3 | frontx: recursive call not in tail position self.a |  |
| 41 | `Grad.RtStop.den` | Shader.lean:625 | 3 | frontx: recursive call not in tail position self.den |  |
| 42 | `Lighting.V3.z` | Filter/Lighting.lean:192 | 3 | frontx: recursive call not in tail position self.z |  |
| 43 | `Shape.GInfo.ccc` | Shape.lean:76 | 3 | frontx: recursive call not in tail position self.ccc |  |
| 44 | `Shape.GInfo.ipos` | Shape.lean:89 | 3 | frontx: recursive call not in tail position self.ipos |  |
| 45 | `Shape.FeatureInfo.stagePos` | Shape.lean:305 | 4 | frontx: recursive call not in tail position self.stagePos |  |
| 46 | `Svg.SubCfg.nested` | Svg.lean:3883 | 4 | frontx: recursive call not in tail position (accumulator mode needs a `Nat` result) |  |
| 47 | `Grad.RtStop.recip` | Shader.lean:628 | 8 | frontx: recursive call not in tail position self.recip |  |

### 1.6 step proof fails (front-end limit; e.g. u8/shift facts)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `F32.isNeg` | Canvas.lean:382 | 1 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.and (BExp.var 4) (BExp.const 1#64)) |  |
| 2 | `Font.u16` | Font.lean:120 | 1 | No goals to be solved frontx: could not prove |  |
| 3 | `F32.neg` | Canvas.lean:466 | 2 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.xor (BExp.var 4) (BExp.const 1#64)) |  |
| 4 | `FilterFrame.chan` | FilterFrame.lean:130 | 2 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.and (BExp.bin Op.lshr (BExp.var 4)  |  |
| 5 | `Font.u32` | Font.lean:121 | 2 | No goals to be solved frontx: could not prove |  |
| 6 | `Clip.cov8` | Clip.lean:102 | 3 | frontx: could not prove BExp.denote σ.env |  |
| 7 | `Clip.div255` | Clip.lean:94 | 3 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.lshr (BExp.bin Op.add (BExp.var 4)  |  |
| 8 | `F32.mk` | Canvas.lean:383 | 3 | No goals to be solved No goals to be solved |  |
| 9 | `GifDecode.le16` | GifDecode.lean:42 | 3 | No goals to be solved frontx: could not prove |  |
| 10 | `Jpeg.pow2` | Jpeg/Huffman.lean:22 | 3 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.shl (BExp.const 1#64) (BExp.bin Op. |  |
| 11 | `PngDecode.tag` | PngDecode.lean:40 | 3 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.ult (BExp.const 0#64) (BExp.var 1)) |  |
| 12 | `PngDecode.be32` | PngDecode.lean:36 | 4 | frontx: could not prove (BExp.denote ((σ.env.set 5 (r8 (if h : i < b.size then b[i] else 0 |  |
| 13 | `Shape.markRecord` | Shape.lean:1322 | 4 | frontx: could not prove (BExp.denote (σ.env.set 7 (rN (ma + 4 + 4 * markIx))) (BExp.var 7) |  |
| 14 | `Font.valueRecordSize` | Font.lean:430 | 6 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.and (BExp.var 4) (BExp.const 1#64)) |  |
| 15 | `Lighting.isPos` | Filter/Lighting.lean:56 | 6 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.and (BExp.var 4) (BExp.const 1#64)) |  |
| 16 | `PngDecode.paeth` | PngDecode.lean:142 | 6 | frontx: could not prove BExp.denote |  |
| 17 | `Shape.tag` | Shape.lean:324 | 6 | No goals to be solved No goals to be solved |  |
| 18 | `Canvas.div65025` | Canvas.lean:142 | 7 | frontx: could not prove BExp.denote σ.env |  |
| 19 | `Inflate.rev` | Inflate.lean:39 | 7 | No goals to be solved frontx: could not prove |  |
| 20 | `Woff.checksum` | Woff.lean:69 | 7 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.lshr (BExp.bin Op.add (BExp.var 1)  |  |
| 21 | `Bytes.findByte` | Bytes.lean:37 | 8 | frontx: could not prove (BExp.denote σ.env (BExp.var 7)).toNat = x1 |  |
| 22 | `Filter.f32Rat` | Filter.lean:109 | 8 | frontx: could not prove BExp.denote ((σ.env.set 7 (rN v.mant)).set 8 (rN v.expo)) |  |
| 23 | `Font.xAdvanceOffset` | Font.lean:436 | 8 | frontx: could not prove BExp.denote (σ.env.set 6 (rN (fmt &&& 4))) (BExp.bin Op.eq (BExp.v |  |
| 24 | `Turbulence.ratOf` | Filter/Turbulence.lean:52 | 8 | frontx: could not prove BExp.denote ((σ.env.set 7 (rN v.mant)).set 8 (rN v.expo)) (BExp.bi |  |
| 25 | `Woff.read255` | Woff.lean:146 | 8 | No goals to be solved frontx: could not prove |  |
| 26 | `Bytes.startsWith` | Bytes.lean:45 | 9 | frontx: could not prove BExp.denote (σ.env.set 8 (rN (i✝ + s.toUTF8.size))) |  |
| 27 | `Canvas.div255` | Canvas.lean:31 | 9 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.lshr (BExp.bin Op.add (BExp.var 4)  |  |
| 28 | `Render.bandCount` | Render.lean:1002 | 10 | frontx: could not prove BExp.denote (σ.env.set 6 (rN (2 * threads))) |  |
| 29 | `Canvas.isTie` | Canvas.lean:725 | 12 | No goals to be solved frontx: could not prove |  |
| 30 | `bitLength` | Geom.lean:182 | 12 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.xor (BExp.bin Op.eq (BExp.var 7) (B |  |
| 31 | `Canvas.pack` | Canvas.lean:58 | 13 | No goals to be solved No goals to be solved |  |
| 32 | `Brotli.alphabetBits` | Brotli.lean:108 | 14 | frontx: could not prove BExp.denote σ.env (BExp.bin Op.shl (BExp.const 1#64) (BExp.var 6)) |  |
| 33 | `Canvas.storeQ` | Canvas.lean:149 | 14 | frontx: could not prove BExp.denote (σ.env.set 5 (rN (n >>> 8))) |  |
| 34 | `Font.coverageIndex` | Font.lean:385 | 21 | No goals to be solved frontx: could not prove |  |
| 35 | `VertOrient.isUpright` | VertOrient.lean:49 | ? | frontx: could not prove BExp.denote ((σ.env.set 8 (rN ⟨x1, x2⟩.fst)).set 9 (rN ⟨x1, x2⟩.sn |  |

### 1.7 Option of structure / tuple

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `FontSet.Entry.font` | FontSet.lean:82 | 1 | frontx: unsupported result type Option LeanSvg.Font |  |
| 2 | `Grad.RawDef.cx` | Shader.lean:365 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 3 | `Grad.RawDef.cy` | Shader.lean:366 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 4 | `Grad.RawDef.fx` | Shader.lean:368 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 5 | `Grad.RawDef.fy` | Shader.lean:369 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 6 | `Grad.RawDef.r` | Shader.lean:367 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 7 | `Grad.RawDef.spread` | Shader.lean:360 | 1 | frontx: unsupported result type Option LeanSvg.Grad.Spread |  |
| 8 | `Grad.RawDef.x1` | Shader.lean:361 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 9 | `Grad.RawDef.x2` | Shader.lean:363 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 10 | `Grad.RawDef.y1` | Shader.lean:362 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 11 | `Grad.RawDef.y2` | Shader.lean:364 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 12 | `Pat.RawDef.width` | Pattern.lean:78 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 13 | `Pat.RawDef.x` | Pattern.lean:76 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 14 | `Pat.RawDef.y` | Pattern.lean:77 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 15 | `Svg.Frame.sbox` | Svg.lean:3736 | 1 | frontx: unsupported result type Option LeanSvg.Box |  |
| 16 | `Svg.MaskEntry.w` | Svg.lean:511 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 17 | `Svg.MaskEntry.x` | Svg.lean:509 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 18 | `Svg.MaskEntry.y` | Svg.lean:510 | 1 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 19 | `Viewport.AspectRatio.align` | Viewport.lean:28 | 1 | frontx: unsupported result type Option (LeanSvg.Viewport.Pos × LeanSvg.Viewport.Pos) |  |
| 20 | `Filter.ElemCtx.bbox` | Filter.lean:859 | 2 | frontx: unsupported result type Option LeanSvg.Filter.URect |  |
| 21 | `Svg.Frame.bbox` | Svg.lean:3704 | 2 | frontx: unsupported result type Option LeanSvg.Box |  |
| 22 | `Svg.MaskEntry.h` | Svg.lean:512 | 2 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 23 | `FeImage.Spec.pre` | Filter/Image.lean:56 | 3 | frontx: unsupported result type Option LeanSvg.Canvas |  |
| 24 | `Pat.RawDef.height` | Pattern.lean:79 | 3 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 25 | `Svg.ClipUse.bbox` | Svg.lean:424 | 3 | frontx: unsupported result type Option LeanSvg.Box |  |
| 26 | `Svg.ClipUse.shape` | Svg.lean:427 | 3 | frontx: unsupported result type Option (LeanSvg.BasicShape.Spec × LeanSvg.Box) |  |
| 27 | `Svg.Shape.image` | Svg.lean:318 | 3 | frontx: unsupported result type Option LeanSvg.Image.Placed |  |
| 28 | `Grad.RawDef.fr` | Shader.lean:370 | 4 | frontx: unsupported result type Option LeanSvg.Grad.LenPct |  |
| 29 | `Viewport.posOf` | Viewport.lean:32 | 6 | frontx: unsupported result type Option LeanSvg.Viewport.Pos |  |
| 30 | `Svg.CtxUse.bbox` | Svg.lean:412 | 8 | frontx: unsupported result type Option LeanSvg.Box |  |
| 31 | `Grad.pickCommon` | Shader.lean:477 | 10 | frontx: unsupported result type Option α |  |
| 32 | `Svg.ClipUse.sbox` | Svg.lean:430 | 10 | frontx: unsupported result type Option LeanSvg.Box |  |
| 33 | `Pat.pickCommon` | Pattern.lean:162 | 11 | frontx: unsupported result type Option α |  |
| 34 | `Render.Layer.back` | Render.lean:509 | 18 | frontx: unsupported result type Option LeanSvg.FilterFrame.Back |  |
| 35 | `Svg.MaskUse.bbox` | Svg.lean:527 | 18 | frontx: unsupported result type Option LeanSvg.Box |  |

### 1.8 String / Std.Format / Char

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Css.Compound.attrs` | Css.lean:58 | 1 | frontx: unsupported result type Array (String × LeanSvg.Css.AttrOp) |  |
| 2 | `Css.Compound.classes` | Css.lean:57 | 1 | frontx: unsupported result type Array String |  |
| 3 | `Css.ElemInfo.attrs` | Css.lean:102 | 1 | frontx: unsupported result type Array (String × String) |  |
| 4 | `Css.ElemInfo.classes` | Css.lean:101 | 1 | frontx: unsupported result type Array String |  |
| 5 | `Font.tailChunks` | Font.lean:109 | 1 | frontx: unsupported result type Array String |  |
| 6 | `Xml.Scoped.binds` | Xml.lean:86 | 1 | frontx: unsupported result type Array (String × String) |  |
| 7 | `Css.instReprCombinator.repr` | Css.lean:71 | 2 | frontx: unsupported result type Std.Format |  |
| 8 | `Filter.instReprMorphOp.repr` | Filter/Morphology.lean:35 | 2 | frontx: unsupported result type Std.Format |  |
| 9 | `Image.instReprFmt.repr` | Image.lean:208 | 2 | frontx: unsupported result type Std.Format |  |
| 10 | `Svg.DefsScan.clips` | Svg.lean:2867 | 2 | frontx: unsupported result type Array (String × Nat) |  |
| 11 | `Text.instReprAlignmentBaseline.repr` | Baseline.lean:74 | 2 | frontx: unsupported result type Std.Format |  |
| 12 | `Text.instReprFace.repr` | Text.lean:70 | 2 | frontx: unsupported result type Std.Format |  |
| 13 | `Filter.RawPrim.children` | Filter.lean:285 | 3 | frontx: unsupported result type Array (String × Array LeanSvg.Xml.Attr) |  |
| 14 | `Grad.Defs.ids` | Shader.lean:422 | 3 | frontx: unsupported result type Array String |  |
| 15 | `Pat.Defs.ids` | Pattern.lean:130 | 3 | frontx: unsupported result type Array String |  |
| 16 | `Svg.DefsScan.markers` | Svg.lean:2872 | 3 | frontx: unsupported result type Array (String × Nat) |  |
| 17 | `Svg.DefsScan.masks` | Svg.lean:2869 | 3 | frontx: unsupported result type Array (String × Nat) |  |
| 18 | `Grad.instReprKind.repr` | Shader.lean:336 | 4 | frontx: unsupported result type Std.Format |  |
| 19 | `Warn.add` | Warn.lean:26 | 4 | frontx: unsupported result type Array String |  |
| 20 | `Warn.addAll` | Warn.lean:30 | 4 | frontx: unsupported result type Array String |  |
| 21 | `Filter.Table.ids` | Filter.lean:298 | 5 | frontx: unsupported result type Std.HashMap String Nat |  |
| 22 | `Text.instReprAnchor.repr` | Text.lean:186 | 5 | frontx: unsupported result type Std.Format |  |
| 23 | `Viewport.instReprPos.repr` | Viewport.lean:21 | 6 | frontx: unsupported result type Std.Format |  |
| 24 | `instReprCap.repr` | Geom.lean:480 | 6 | frontx: unsupported result type Std.Format |  |
| 25 | `Css.splitWs` | Css.lean:127 | 14 | frontx: unsupported result type Array String |  |
| 26 | `Svg.Doc.warnings` | Svg.lean:625 | 65 | frontx: unsupported result type Array String |  |

### 1.9 body shape not a scalar (do-block / join point)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Font.b64At` | Font.lean:562 | 4 | frontx: not a scalar: { byteIdx := i } |  |
| 2 | `Font.strByte` | Font.lean:1067 | 4 | frontx: not a scalar: { byteIdx := i } |  |
| 3 | `Svg.isShape` | Svg.lean:2569 | 4 | frontx: not a scalar: name |  |
| 4 | `Filter.isPrimitive` | Filter.lean:527 | 6 | frontx: not a scalar: name |  |
| 5 | `FeImage.ownProp` | Filter/Image.lean:195 | 7 | frontx: not a scalar: n |  |
| 6 | `Turbulence.toByte` | Filter/Turbulence.lean:245 | 7 | frontx: not a scalar: if fractal = true then (s.toInt * 255 + 255 * 2 ^ sh + 2 ^ sh).fdiv  |  |
| 7 | `Use.isGraphicTarget` | Use.lean:67 | 7 | frontx: not a scalar: name |  |
| 8 | `Use.isDefLike` | Use.lean:74 | 8 | frontx: not a scalar: name |  |
| 9 | `FamilyMatch.generic` | FamilyMatch.lean:93 | 9 | frontx: not a scalar: lname |  |
| 10 | `Shape.scriptRtl` | ShapeRun.lean:52 | 10 | frontx: not a scalar: iso |  |
| 11 | `Woff.tagOf` | Woff.lean:41 | 12 | frontx: not a scalar: ByteArray.foldlM (fun x1 x2 => pure ((fun acc b => acc * 256 + b.toN |  |
| 12 | `Png.crcBytes` | Png.lean:43 | 13 | frontx: not a scalar: ByteArray.foldlM |  |
| 13 | `Svg.isCssOnlyProp` | Svg.lean:2061 | 13 | frontx: not a scalar: name |  |
| 14 | `F32.bitLen` | Canvas.lean:386 | 35 | frontx: not a scalar: have __do_jp := fun y => |  |

### 1.10 function-typed value (closure)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Image.hasByte` | Image.lean:52 | 5 | frontx: unsupported parameter type UInt8 → Bool |  |
| 2 | `Bytes.skipWhile` | Bytes.lean:25 | 7 | frontx: unsupported parameter type UInt8 → Bool |  |
| 3 | `Css.scanFor` | Css.lean:108 | 9 | frontx: unsupported parameter type UInt8 → Bool |  |

### 1.11 match shape (multi-scrutinee, Bool-pair, literal patterns, Decidable.rec)

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Font.Tables.cmap` | Font.lean:171 | 1 | frontx: unsupported term match self.3 with |  |
| 2 | `Font.Tables.glyf` | Font.lean:173 | 1 | frontx: unsupported term match self.5 with |  |
| 3 | `Font.Tables.gpos` | Font.lean:177 | 1 | frontx: unsupported term match self.9 with |  |
| 4 | `Font.Tables.head` | Font.lean:169 | 1 | frontx: unsupported term match self.1 with |  |
| 5 | `Font.Tables.hhea` | Font.lean:174 | 1 | frontx: unsupported term match self.6 with |  |
| 6 | `Font.Tables.hmtx` | Font.lean:175 | 1 | frontx: unsupported term match self.7 with |  |
| 7 | `Font.Tables.kernT` | Font.lean:176 | 1 | frontx: unsupported term match self.8 with |  |
| 8 | `Font.Tables.loca` | Font.lean:172 | 1 | frontx: unsupported term match self.4 with |  |
| 9 | `Font.Tables.maxp` | Font.lean:170 | 1 | frontx: unsupported term match self.2 with |  |
| 10 | `Font.Tables.post` | Font.lean:178 | 1 | frontx: unsupported term match self.10 with |  |
| 11 | `Font.Tables.os2` | Font.lean:179 | 2 | frontx: unsupported term match self.11 with |  |
| 12 | `Svg.SubCfg.outSize` | Svg.lean:3887 | 2 | frontx: unsupported term match self.3 with |  |
| 13 | `F32.p2` | Canvas.lean:362 | 18 | frontx: unsupported term Decidable.rec (fun h => (fun x => 0) h) (fun h => (fun h => LeanS |  |

### 1.12 variable x variable `*` (Nat), nonlinear bound

| # | function | file:line | ≈lines | first-failure message | ⚠ |
|---|---|---|---|---|---|
| 1 | `Clip.cov16` | Clip.lean:105 | 3 | frontx: `(a * 65536 + 254) / 255` is translated by one conditional subtraction and needs a |  ⚠ |
| 2 | `Image.premulU8` | Image.lean:235 | 5 | frontx: unsupported term instHMul.1 c a |  ⚠ |
| 3 | `Jpeg.peekBits` | Jpeg/Huffman.lean:25 | 7 | frontx: unsupported term instHMul.1 (LeanSvg.Jpeg.byteAt d (pos / 8)).toUInt32 65536 |  ⚠ |
| 4 | `Grad.stopAlpha8` | Shader.lean:891 | 8 | frontx: `alpha * stopOp * fillOp * groupOp * 2 / LeanSvg.Grad.opacityCube` is translated b |  ⚠ |
| 5 | `Pat.opacityQ` | PatternRender.lean:200 | 8 | frontx: `o * LeanSvg.Canvas.opGrid * 2 / LeanSvg.Svg.opacityOne` is translated by one cond |  ⚠ |
| 6 | `Svg.mulOpacity` | Svg.lean:1019 | 8 | frontx: `a * b * 2 / LeanSvg.Svg.opacityOne` is translated by one conditional subtraction  |  ⚠ |
| 7 | `Canvas.premul` | Canvas.lean:40 | 9 | frontx: `(c * a + 127) / 255` is translated by one conditional subtraction and needs c * a |  ⚠ |
| 8 | `Lighting.mulQ` | Filter/Lighting.lean:292 | 9 | frontx: unsupported term instHMul.1 (a >>> 22) (b >>> 22) |  ⚠ |
| 9 | `Png.zlibLen` | Png.lean:162 | 9 | frontx: unsupported term instHMul.1 h (rowBytes + 1) |  ⚠ |
| 10 | `PngDecode.sample` | PngDecode.lean:215 | 10 | frontx: unsupported term instHMul.1 x ch |  ⚠ |
| 11 | `FilterApply.iirCoeffs` | FilterApply.lean:385 | 12 | frontx: unsupported term instHMul.1 s16 s16 |  ⚠ |
| 12 | `Grad.lerpDown` | Shader.lean:761 | 12 | frontx: unsupported term instHMul.1 (2 * cl + 1) den |  ⚠ |
| 13 | `Render.opacityQ` | Render.lean:464 | 13 | frontx: `o * LeanSvg.Canvas.opGrid * 2 / LeanSvg.Svg.opacityOne` is translated by one cond |  ⚠ |
| 14 | `Svg.opacityToU8` | Svg.lean:1027 | 18 | frontx: `alpha * fillOp * groupOp * 2 / (LeanSvg.Svg.opacityOne * LeanSvg.Svg.opacityOne)` |  ⚠ |
| 15 | `Grad.lerpUp` | Shader.lean:734 | 27 | frontx: unsupported term instHMul.1 (2 * cl + 1) den |  ⚠ |

## 2. Possibly unblocked by NOTES §22 (var×var `*`, `/` `%` by variable)

Rows with S(f) ⊆ {var×var `*`, `/`/`%` by a variable} and a known closure. Re-probe with the current `frontx_compile` before counting these as blocked.

22 functions.

| # | function | file:line | ≈lines | S(f) | own first failure |
|---|---|---|---|---|---|
| 1 | `Clip.cov16` | Clip.lean:105 | 3 | var×var `*` | var×var `*` |
| 2 | `Grad.recipOf` | Shader.lean:730 | 4 | `/` `%` by var | `/` `%` by var |
| 3 | `Image.premulU8` | Image.lean:235 | 5 | var×var `*` | var×var `*` |
| 4 | `PngDecode.to8` | PngDecode.lean:225 | 6 | `/` `%` by var | `/` `%` by var |
| 5 | `Jpeg.peekBits` | Jpeg/Huffman.lean:25 | 7 | var×var `*` | var×var `*` |
| 6 | `Grad.stopAlpha8` | Shader.lean:891 | 8 | var×var `*` | var×var `*` |
| 7 | `Pat.opacityQ` | PatternRender.lean:200 | 8 | var×var `*` | var×var `*` |
| 8 | `Svg.mulOpacity` | Svg.lean:1019 | 8 | var×var `*` | var×var `*` |
| 9 | `Canvas.premul` | Canvas.lean:40 | 9 | var×var `*` | var×var `*` |
| 10 | `Canvas.unpremul` | Canvas.lean:49 | 9 | `/` `%` by var | `/` `%` by var |
| 11 | `Inflate.peek` | Inflate.lean:26 | 9 | `/` `%` by var | `/` `%` by var |
| 12 | `Lighting.mulQ` | Filter/Lighting.lean:292 | 9 | var×var `*` | var×var `*` |
| 13 | `Png.zlibLen` | Png.lean:162 | 9 | var×var `*` | var×var `*` |
| 14 | `Lighting.expS` | Filter/Lighting.lean:224 | 10 | `/` `%` by var, var×var `*` | var×var `*` |
| 15 | `PngDecode.sample` | PngDecode.lean:215 | 10 | var×var `*` | var×var `*` |
| 16 | `FilterApply.iirCoeffs` | FilterApply.lean:385 | 12 | var×var `*` | var×var `*` |
| 17 | `Grad.lerpDown` | Shader.lean:761 | 12 | var×var `*` | var×var `*` |
| 18 | `Render.opacityQ` | Render.lean:464 | 13 | var×var `*` | var×var `*` |
| 19 | `PngDecode.passLen` | PngDecode.lean:128 | 14 | `/` `%` by var | `/` `%` by var |
| 20 | `Lighting.atanh2` | Filter/Lighting.lean:209 | 15 | `/` `%` by var | `/` `%` by var |
| 21 | `Svg.opacityToU8` | Svg.lean:1027 | 18 | var×var `*` | var×var `*` |
| 22 | `Grad.lerpUp` | Shader.lean:734 | 27 | var×var `*` | var×var `*` |

## 3. Leaves (no user-defined callee) and the feature that blocks each

1251 leaves: 33 OK, 1148 FAIL, 70 NOOUT. Sorted: OK first, then smallest.

| function | file:line | ≈lines | status | needed feature (own first failure) |
|---|---|---|---|---|
| `Bytes.isAlpha` | Bytes.lean:20 | 1 | OK | — |
| `Bytes.isDigit` | Bytes.lean:19 | 1 | OK | — |
| `Bytes.isWs` | Bytes.lean:18 | 1 | OK | — |
| `ConvolveMatrix.cB` | Filter/ConvolveMatrix.lean:27 | 1 | OK | — |
| `ConvolveMatrix.cG` | Filter/ConvolveMatrix.lean:26 | 1 | OK | — |
| `ConvolveMatrix.cR` | Filter/ConvolveMatrix.lean:25 | 1 | OK | — |
| `F32.expo` | Canvas.lean:381 | 1 | OK | — |
| `F32.mant` | Canvas.lean:380 | 1 | OK | — |
| `FilterApply.chB` | FilterApply.lean:83 | 1 | OK | — |
| `FilterApply.chG` | FilterApply.lean:82 | 1 | OK | — |
| `FilterApply.chR` | FilterApply.lean:81 | 1 | OK | — |
| `Bytes.toLower` | Bytes.lean:23 | 2 | OK | — |
| `ConvolveMatrix.cA` | Filter/ConvolveMatrix.lean:28 | 2 | OK | — |
| `FilterApply.chA` | FilterApply.lean:84 | 2 | OK | — |
| `ForeignObject.isWs` | ForeignObject.lean:231 | 2 | OK | — |
| `Image.isAsciiWs` | Image.lean:49 | 3 | OK | — |
| `Image.isTabNl` | Image.lean:46 | 3 | OK | — |
| `Jpeg.byteAt` | Jpeg/Huffman.lean:19 | 3 | OK | — |
| `Shape.maxLenFor` | Shape.lean:54 | 3 | OK | — |
| `ShapeText.utf8Len` | ShapeText.lean:62 | 3 | OK | — |
| `Bytes.at'` | Bytes.lean:14 | 4 | OK | — |
| `Filter.isKnownUnsupported` | Filter.lean:523 | 4 | OK | — |
| `PngDecode.channels` | PngDecode.lean:50 | 4 | OK | — |
| `Text.isHan` | Text.lean:118 | 5 | OK | — |
| `PngDecode.validDepth` | PngDecode.lean:54 | 6 | OK | — |
| `Shape.opsFor` | Shape.lean:57 | 7 | OK | — |
| `Text.isWordSep` | Text.lean:433 | 7 | OK | — |
| `FilterApply.dispChan` | Filter/DisplacementMap.lean:22 | 8 | OK | — |
| `Shape.isDefaultIgnorable` | Shape.lean:132 | 8 | OK | — |
| `Font.cmapScore` | Font.lean:212 | 9 | OK | — |
| `Image.b64Val` | Image.lean:92 | 9 | OK | — |
| `Font.b64Digit` | Font.lean:551 | 11 | OK | — |
| `FamilyMatch.suite` | FamilyMatch.lean:56 | 22 | OK | — |
| `Grad.instBEqKind.beq` | Shader.lean:336 | 0 | FAIL | structure param/result |
| `Image.instBEqFmt.beq` | Image.lean:208 | 0 | FAIL | structure param/result |
| `Text.instBEqAlignmentBaseline.beq` | Baseline.lean:74 | 0 | FAIL | structure param/result |
| `instBEqCap.beq` | Geom.lean:480 | 0 | FAIL | structure param/result |
| `BasicShape.Env.len` | BasicShape.lean:82 | 1 | FAIL | Int/Fx |
| `BasicShape.Env.mk` | BasicShape.lean:81 | 1 | FAIL | ctor/projection |
| `BasicShape.Geo.circle` | BasicShape.lean:62 | 1 | FAIL | ctor/projection |
| `BasicShape.Geo.ellipse` | BasicShape.lean:63 | 1 | FAIL | ctor/projection |
| `BasicShape.Geo.polygon` | BasicShape.lean:68 | 1 | FAIL | ctor/projection |
| `BasicShape.LP.abs` | BasicShape.lean:42 | 1 | FAIL | Int/Fx |
| `BasicShape.LP.mk` | BasicShape.lean:41 | 1 | FAIL | ctor/projection |
| `BasicShape.LP.pct` | BasicShape.lean:43 | 1 | FAIL | Int/Fx |
| `BasicShape.Spec.geo` | BasicShape.lean:75 | 1 | FAIL | structure param/result |
| `BasicShape.Spec.mk` | BasicShape.lean:74 | 1 | FAIL | ctor/projection |
| `Box.mk` | Geom.lean:332 | 1 | FAIL | ctor/projection |
| `Box.x0` | Geom.lean:333 | 1 | FAIL | Int/Fx |
| `Box.x1` | Geom.lean:335 | 1 | FAIL | Int/Fx |
| `Box.y0` | Geom.lean:334 | 1 | FAIL | Int/Fx |
| `Brotli.Blocks.counts` | Brotli.lean:244 | 1 | FAIL | structure param/result |
| `Brotli.Blocks.cur` | Brotli.lean:245 | 1 | FAIL | structure param/result |
| `Brotli.Blocks.last2` | Brotli.lean:246 | 1 | FAIL | structure param/result |
| `Brotli.Blocks.mk` | Brotli.lean:241 | 1 | FAIL | ctor/projection |
| `Brotli.Blocks.n` | Brotli.lean:242 | 1 | FAIL | structure param/result |
| `Brotli.Blocks.types` | Brotli.lean:243 | 1 | FAIL | structure param/result |
| `Brotli.Code.count` | Brotli.lean:64 | 1 | FAIL | Array |
| `Brotli.Code.mk` | Brotli.lean:62 | 1 | FAIL | ctor/projection |
| `Brotli.Code.single` | Brotli.lean:63 | 1 | FAIL | structure param/result |
| `Canvas.h` | Canvas.lean:25 | 1 | FAIL | structure param/result |
| `Canvas.mk` | Canvas.lean:23 | 1 | FAIL | ctor/projection |
| `Canvas.w` | Canvas.lean:24 | 1 | FAIL | structure param/result |
| `Clip.Mask.h` | Clip.lean:90 | 1 | FAIL | structure param/result |
| `Clip.Mask.mk` | Clip.lean:86 | 1 | FAIL | ctor/projection |
| `Clip.Mask.w` | Clip.lean:89 | 1 | FAIL | structure param/result |
| `Clip.Mask.x0` | Clip.lean:87 | 1 | FAIL | structure param/result |
| `Clip.Mask.y0` | Clip.lean:88 | 1 | FAIL | structure param/result |
| `Css.AttrOp.contains` | Css.lean:49 | 1 | FAIL | ctor/projection |
| `Css.AttrOp.eq` | Css.lean:48 | 1 | FAIL | ctor/projection |
| `Css.Component.comb` | Css.lean:76 | 1 | FAIL | structure param/result |
| `Css.Compound.attrs` | Css.lean:58 | 1 | FAIL | String/Format/Char |
| `Css.Compound.classes` | Css.lean:57 | 1 | FAIL | String/Format/Char |
| `Css.Compound.hasType` | Css.lean:54 | 1 | FAIL | ctor/projection |
| `Css.Compound.id` | Css.lean:56 | 1 | FAIL | ctor/projection |
| `Css.Compound.mk` | Css.lean:53 | 1 | FAIL | ctor/projection |
| `Css.Compound.typeName` | Css.lean:55 | 1 | FAIL | ctor/projection |
| `Css.Decl.mk` | Css.lean:86 | 1 | FAIL | ctor/projection |
| `Css.Decl.name` | Css.lean:87 | 1 | FAIL | ctor/projection |
| `Css.Decl.value` | Css.lean:88 | 1 | FAIL | Array |
| `Css.ElemInfo.attrs` | Css.lean:102 | 1 | FAIL | String/Format/Char |
| `Css.ElemInfo.classes` | Css.lean:101 | 1 | FAIL | String/Format/Char |
| `Css.ElemInfo.id` | Css.lean:100 | 1 | FAIL | ctor/projection |
| `Css.ElemInfo.mk` | Css.lean:98 | 1 | FAIL | ctor/projection |
| `Css.ElemInfo.tag` | Css.lean:99 | 1 | FAIL | ctor/projection |
| `Css.Rule.decls` | Css.lean:94 | 1 | FAIL | Array |
| `Css.Rule.mk` | Css.lean:92 | 1 | FAIL | ctor/projection |
| `Css.Rule.selector` | Css.lean:93 | 1 | FAIL | structure param/result |
| `Css.Selector.components` | Css.lean:82 | 1 | FAIL | Array |
| `DSeg.mk` | Geom.lean:844 | 1 | FAIL | ctor/projection |
| `DSeg.p` | Geom.lean:845 | 1 | FAIL | Int/Fx |
| `DSeg.q` | Geom.lean:846 | 1 | FAIL | Int/Fx |
| `DSeg.tp` | Geom.lean:847 | 1 | FAIL | Int/Fx |
| `F32.isNeg` | Canvas.lean:382 | 1 | FAIL | step proof |
| `FeImage.Href.elem` | Filter/Image.lean:42 | 1 | FAIL | ctor/projection |
| `FeImage.Job.mk` | Filter/ImageRender.lean:17 | 1 | FAIL | ctor/projection |
| `FeImage.Job.prim` | Filter/ImageRender.lean:18 | 1 | FAIL | structure param/result |
| `FeImage.Job.rh` | Filter/ImageRender.lean:21 | 1 | FAIL | structure param/result |
| `FeImage.Job.rw` | Filter/ImageRender.lean:20 | 1 | FAIL | structure param/result |
| `FeImage.Job.spec` | Filter/ImageRender.lean:19 | 1 | FAIL | structure param/result |
| `FeImage.Job.sx` | Filter/ImageRender.lean:22 | 1 | FAIL | Int/Fx |
| `FeImage.Job.uw` | Filter/ImageRender.lean:30 | 1 | FAIL | Int/Fx |
| `FeImage.Spec.href` | Filter/Image.lean:49 | 1 | FAIL | structure param/result |
| `FeImage.Spec.mk` | Filter/Image.lean:48 | 1 | FAIL | ctor/projection |
| `Filter.CMKind.matrix` | Filter.lean:168 | 1 | FAIL | ctor/projection |
| `Filter.CMKind.saturate` | Filter.lean:169 | 1 | FAIL | ctor/projection |
| `Filter.ElemCtx.color` | Filter.lean:861 | 1 | FAIL | structure param/result |
| `Filter.ElemCtx.vbW` | Filter.lean:864 | 1 | FAIL | Int/Fx |
| `Filter.Kind.blend` | Filter.lean:199 | 1 | FAIL | ctor/projection |
| `Filter.Kind.blur` | Filter.lean:196 | 1 | FAIL | ctor/projection |
| `Filter.Kind.colorMatrix` | Filter.lean:201 | 1 | FAIL | ctor/projection |
| `Filter.Kind.composite` | Filter.lean:200 | 1 | FAIL | ctor/projection |
| `Filter.Kind.dropShadow` | Filter.lean:197 | 1 | FAIL | ctor/projection |
| `Filter.Kind.flood` | Filter.lean:194 | 1 | FAIL | ctor/projection |
| `Filter.Kind.image` | Filter.lean:203 | 1 | FAIL | ctor/projection |
| `Filter.Kind.lighting` | Filter.lean:210 | 1 | FAIL | ctor/projection |
| `Filter.Kind.merge` | Filter.lean:198 | 1 | FAIL | ctor/projection |
| `Filter.Kind.morphology` | Filter.lean:205 | 1 | FAIL | ctor/projection |
| `Filter.Kind.offset` | Filter.lean:195 | 1 | FAIL | ctor/projection |
| `Filter.Kind.tile` | Filter.lean:211 | 1 | FAIL | ctor/projection |
| `Filter.Kind.transfer` | Filter.lean:202 | 1 | FAIL | ctor/projection |
| `Filter.Kind.turbulence` | Filter.lean:204 | 1 | FAIL | ctor/projection |
| `Filter.Len.num` | Filter.lean:427 | 1 | FAIL | ctor/projection |
| `Filter.Parsers.color` | Filter.lean:304 | 1 | FAIL | other: invalid instantiateFo |
| `Filter.Parsers.mk` | Filter.lean:303 | 1 | FAIL | ctor/projection |
| `Filter.Parsers.opacity` | Filter.lean:305 | 1 | FAIL | other: invalid instantiateFo |
| `Filter.Prim.linear` | Filter.lean:238 | 1 | FAIL | structure param/result |
| `Filter.RawFilter.attrs` | Filter.lean:290 | 1 | FAIL | Array |
| `Filter.RawFilter.id` | Filter.lean:289 | 1 | FAIL | ctor/projection |
| `Filter.RawFilter.mk` | Filter.lean:288 | 1 | FAIL | ctor/projection |
| `Filter.RawPrim.attrs` | Filter.lean:277 | 1 | FAIL | Array |
| `Filter.RawPrim.floodColor` | Filter.lean:283 | 1 | FAIL | Array |
| `Filter.RawPrim.floodOpacity` | Filter.lean:284 | 1 | FAIL | Array |
| `Filter.RawPrim.linear` | Filter.lean:278 | 1 | FAIL | ctor/projection |
| `Filter.RawPrim.mk` | Filter.lean:275 | 1 | FAIL | ctor/projection |
| `Filter.RawPrim.name` | Filter.lean:276 | 1 | FAIL | ctor/projection |
| `Filter.Resolved.mk` | Filter.lean:247 | 1 | FAIL | ctor/projection |
| `Filter.Resolved.region` | Filter.lean:248 | 1 | FAIL | structure param/result |
| `Filter.TF.discrete` | Filter.lean:179 | 1 | FAIL | ctor/projection |
| `Filter.TF.linear` | Filter.lean:180 | 1 | FAIL | ctor/projection |
| `Filter.TF.table` | Filter.lean:178 | 1 | FAIL | ctor/projection |
| `Filter.Table.filters` | Filter.lean:297 | 1 | FAIL | Array |
| `Filter.Table.mk` | Filter.lean:296 | 1 | FAIL | ctor/projection |
| `Filter.URect.h` | Filter.lean:231 | 1 | FAIL | Int/Fx |
| `Filter.URect.mk` | Filter.lean:227 | 1 | FAIL | ctor/projection |
| `Filter.URect.w` | Filter.lean:230 | 1 | FAIL | Int/Fx |
| `Filter.URect.x` | Filter.lean:228 | 1 | FAIL | Int/Fx |
| `Filter.URect.y` | Filter.lean:229 | 1 | FAIL | Int/Fx |
| `FilterApply.Img.cv` | FilterApply.lean:107 | 1 | FAIL | structure param/result |
| `FilterApply.Img.mk` | FilterApply.lean:106 | 1 | FAIL | ctor/projection |
| `FilterApply.Img.rh` | FilterApply.lean:111 | 1 | FAIL | Int/Fx |
| `FilterApply.Img.rw` | FilterApply.lean:110 | 1 | FAIL | Int/Fx |
| `FilterApply.Img.rx` | FilterApply.lean:108 | 1 | FAIL | Int/Fx |
| `FilterApply.Img.ry` | FilterApply.lean:109 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.k11` | FilterFrame.lean:36 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.k12` | FilterFrame.lean:37 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.k21` | FilterFrame.lean:38 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.k22` | FilterFrame.lean:39 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.mk` | FilterFrame.lean:35 | 1 | FAIL | ctor/projection |
| `FilterFrame.Back.tx` | FilterFrame.lean:40 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.ty` | FilterFrame.lean:41 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.vx` | FilterFrame.lean:47 | 1 | FAIL | Int/Fx |
| `FilterFrame.Back.x0` | FilterFrame.lean:42 | 1 | FAIL | Int/Fx |
| `FilterFrame.Plan.mk` | FilterFrame.lean:52 | 1 | FAIL | ctor/projection |
| `FilterFrame.Plan.root` | FilterFrame.lean:58 | 1 | FAIL | Int/Fx |
| `FilterFrame.Plan.w` | FilterFrame.lean:53 | 1 | FAIL | structure param/result |
| `Font.Tables.cmap` | Font.lean:171 | 1 | FAIL | match shape |
| `Font.Tables.glyf` | Font.lean:173 | 1 | FAIL | match shape |
| `Font.Tables.gpos` | Font.lean:177 | 1 | FAIL | match shape |
| `Font.Tables.head` | Font.lean:169 | 1 | FAIL | match shape |
| `Font.Tables.hhea` | Font.lean:174 | 1 | FAIL | match shape |
| `Font.Tables.hmtx` | Font.lean:175 | 1 | FAIL | match shape |
| `Font.Tables.kernT` | Font.lean:176 | 1 | FAIL | match shape |
| `Font.Tables.loca` | Font.lean:172 | 1 | FAIL | match shape |
| `Font.Tables.maxp` | Font.lean:170 | 1 | FAIL | match shape |
| `Font.Tables.mk` | Font.lean:168 | 1 | FAIL | ctor/projection |
| `Font.Tables.post` | Font.lean:178 | 1 | FAIL | match shape |
| `Font.cmapSorted` | Font.lean:81 | 1 | FAIL | structure param/result |
| `Font.glyfOff` | Font.lean:73 | 1 | FAIL | structure param/result |
| `Font.indexToLocFormat` | Font.lean:71 | 1 | FAIL | structure param/result |
| `Font.kernPairsOff` | Font.lean:87 | 1 | FAIL | structure param/result |
| `Font.locaOff` | Font.lean:72 | 1 | FAIL | structure param/result |
| `Font.mk` | Font.lean:42 | 1 | FAIL | ctor/projection |
| `Font.numberOfHMetrics` | Font.lean:82 | 1 | FAIL | structure param/result |
| `Font.strikeoutPosition` | Font.lean:102 | 1 | FAIL | Int/Fx |
| `Font.tailChunkBytes` | Font.lean:110 | 1 | FAIL | structure param/result |
| `Font.tailChunks` | Font.lean:109 | 1 | FAIL | String/Format/Char |
| `Font.unitsPerEm` | Font.lean:43 | 1 | FAIL | structure param/result |
| `FontFace.Face.family` | FontFace.lean:47 | 1 | FAIL | Array |
| `FontFace.Face.font` | FontFace.lean:50 | 1 | FAIL | structure param/result |
| `FontFace.Face.italic` | FontFace.lean:49 | 1 | FAIL | structure param/result |
| `FontFace.Face.mk` | FontFace.lean:46 | 1 | FAIL | ctor/projection |
| `FontFace.Face.weight` | FontFace.lean:48 | 1 | FAIL | structure param/result |
| `FontSet.Entry.family` | FontSet.lean:81 | 1 | FAIL | ctor/projection |
| `FontSet.Entry.font` | FontSet.lean:82 | 1 | FAIL | Option/tuple |
| `FontSet.Entry.mk` | FontSet.lean:80 | 1 | FAIL | ctor/projection |
| `ForeignObject.HStyle.italic` | ForeignObject.lean:68 | 1 | FAIL | structure param/result |
| `ForeignObject.HStyle.lineHeight` | ForeignObject.lean:74 | 1 | FAIL | Int/Fx |
| `ForeignObject.HStyle.mk` | ForeignObject.lean:63 | 1 | FAIL | ctor/projection |
| `ForeignObject.HStyle.size` | ForeignObject.lean:66 | 1 | FAIL | Int/Fx |
| `ForeignObject.HStyle.weight` | ForeignObject.lean:67 | 1 | FAIL | structure param/result |
| `ForeignObject.HStyle.wrap` | ForeignObject.lean:75 | 1 | FAIL | structure param/result |
| `ForeignObject.Item.text` | ForeignObject.lean:79 | 1 | FAIL | ctor/projection |
| `ForeignObject.Line.mk` | ForeignObject.lean:252 | 1 | FAIL | ctor/projection |
| `ForeignObject.Line.pieces` | ForeignObject.lean:253 | 1 | FAIL | Array |
| `Fx.abs` | Fixed.lean:41 | 1 | FAIL | Int/Fx |
| `Fx.ceil` | Fixed.lean:39 | 1 | FAIL | Int/Fx |
| `Fx.floor` | Fixed.lean:38 | 1 | FAIL | Int/Fx |
| `Fx.min` | Fixed.lean:42 | 1 | FAIL | Int/Fx |
| `Fx.round` | Fixed.lean:40 | 1 | FAIL | Int/Fx |
| `Grad.Aff.a` | Shader.lean:183 | 1 | FAIL | Int/Fx |
| `Grad.Aff.b` | Shader.lean:184 | 1 | FAIL | Int/Fx |
| `Grad.Aff.c` | Shader.lean:185 | 1 | FAIL | Int/Fx |
| `Grad.Aff.d` | Shader.lean:186 | 1 | FAIL | Int/Fx |
| `Grad.Aff.e` | Shader.lean:187 | 1 | FAIL | Int/Fx |
| `Grad.Aff.mk` | Shader.lean:182 | 1 | FAIL | ctor/projection |
| `Grad.Axis.aH` | Shader.lean:657 | 1 | FAIL | Int/Fx |
| `Grad.Axis.aL` | Shader.lean:660 | 1 | FAIL | structure param/result |
| `Grad.Axis.cH` | Shader.lean:658 | 1 | FAIL | Int/Fx |
| `Grad.Axis.cL` | Shader.lean:661 | 1 | FAIL | structure param/result |
| `Grad.Axis.eH` | Shader.lean:659 | 1 | FAIL | Int/Fx |
| `Grad.Axis.mk` | Shader.lean:656 | 1 | FAIL | ctor/projection |
| `Grad.Defs.mk` | Shader.lean:415 | 1 | FAIL | ctor/projection |
| `Grad.PctRef.mk` | Shader.lean:505 | 1 | FAIL | ctor/projection |
| `Grad.PctRef.w` | Shader.lean:506 | 1 | FAIL | Int/Fx |
| `Grad.RawDef.cx` | Shader.lean:365 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.cy` | Shader.lean:366 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.fx` | Shader.lean:368 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.fy` | Shader.lean:369 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.id` | Shader.lean:354 | 1 | FAIL | ctor/projection |
| `Grad.RawDef.kind` | Shader.lean:355 | 1 | FAIL | structure param/result |
| `Grad.RawDef.mk` | Shader.lean:353 | 1 | FAIL | ctor/projection |
| `Grad.RawDef.oBB` | Shader.lean:358 | 1 | FAIL | ctor/projection |
| `Grad.RawDef.r` | Shader.lean:367 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.spread` | Shader.lean:360 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.transform` | Shader.lean:359 | 1 | FAIL | Int/Fx |
| `Grad.RawDef.x1` | Shader.lean:361 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.x2` | Shader.lean:363 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.y1` | Shader.lean:362 | 1 | FAIL | Option/tuple |
| `Grad.RawDef.y2` | Shader.lean:364 | 1 | FAIL | Option/tuple |
| `Grad.RawStop.col` | Shader.lean:342 | 1 | FAIL | structure param/result |
| `Grad.RawStop.mk` | Shader.lean:340 | 1 | FAIL | ctor/projection |
| `Grad.RawStop.off` | Shader.lean:341 | 1 | FAIL | Int/Fx |
| `Grad.Resolved.mk` | Shader.lean:405 | 1 | FAIL | ctor/projection |
| `Grad.Resolved.oBB` | Shader.lean:407 | 1 | FAIL | structure param/result |
| `Grad.Resolved.shape` | Shader.lean:406 | 1 | FAIL | structure param/result |
| `Grad.Resolved.spread` | Shader.lean:409 | 1 | FAIL | structure param/result |
| `Grad.Resolved.transform` | Shader.lean:408 | 1 | FAIL | Int/Fx |
| `Grad.Rt.geom` | Shader.lean:679 | 1 | FAIL | structure param/result |
| `Grad.Rt.mk` | Shader.lean:678 | 1 | FAIL | ctor/projection |
| `Grad.Rt.px` | Shader.lean:682 | 1 | FAIL | structure param/result |
| `Grad.Rt.py` | Shader.lean:683 | 1 | FAIL | structure param/result |
| `Grad.RtStop.b` | Shader.lean:621 | 1 | FAIL | recursion |
| `Grad.RtStop.g` | Shader.lean:620 | 1 | FAIL | recursion |
| `Grad.RtStop.off` | Shader.lean:618 | 1 | FAIL | recursion |
| `Grad.RtStop.r` | Shader.lean:619 | 1 | FAIL | recursion |
| `Image.Pix.h` | Image.lean:231 | 1 | FAIL | structure param/result |
| `Image.Pix.mk` | Image.lean:229 | 1 | FAIL | ctor/projection |
| `Image.Pix.w` | Image.lean:230 | 1 | FAIL | structure param/result |
| `Image.Placed.mk` | Image.lean:298 | 1 | FAIL | ctor/projection |
| `Image.Placed.pix` | Image.lean:299 | 1 | FAIL | structure param/result |
| `Image.Placed.vh` | Image.lean:303 | 1 | FAIL | Int/Fx |
| `Image.Placed.vw` | Image.lean:302 | 1 | FAIL | Int/Fx |
| `Image.Placed.vx` | Image.lean:300 | 1 | FAIL | Int/Fx |
| `Image.Placed.vy` | Image.lean:301 | 1 | FAIL | Int/Fx |
| `Image.Rt.mk` | Image.lean:352 | 1 | FAIL | ctor/projection |
| `Image.Rt.pix` | Image.lean:353 | 1 | FAIL | structure param/result |
| `Image.Rt.px` | Image.lean:354 | 1 | FAIL | structure param/result |
| `Image.Rt.py` | Image.lean:355 | 1 | FAIL | structure param/result |
| `ImageData.Decoded.h` | ImageData.lean:21 | 1 | FAIL | recursion |
| `ImageData.Decoded.mk` | ImageData.lean:19 | 1 | FAIL | ctor/projection |
| `ImageData.Decoded.w` | ImageData.lean:20 | 1 | FAIL | recursion |
| `Inflate.Huff.bits` | Inflate.lean:36 | 1 | FAIL | structure param/result |
| `Inflate.Huff.mk` | Inflate.lean:35 | 1 | FAIL | ctor/projection |
| `Jpeg.Huff.offset` | Jpeg/Huffman.lean:48 | 1 | FAIL | Array |
| `JpegDecode.Comp.bw` | JpegDecode.lean:89 | 1 | FAIL | recursion |
| `JpegDecode.Comp.h` | JpegDecode.lean:85 | 1 | FAIL | recursion |
| `JpegDecode.Comp.id` | JpegDecode.lean:84 | 1 | FAIL | recursion |
| `JpegDecode.Comp.mk` | JpegDecode.lean:83 | 1 | FAIL | ctor/projection |
| `JpegDecode.Comp.v` | JpegDecode.lean:86 | 1 | FAIL | recursion |
| `JpegDecode.Frame.comps` | JpegDecode.lean:96 | 1 | FAIL | Array |
| `JpegDecode.Frame.h` | JpegDecode.lean:95 | 1 | FAIL | structure param/result |
| `JpegDecode.Frame.hmax` | JpegDecode.lean:97 | 1 | FAIL | structure param/result |
| `JpegDecode.Frame.mcux` | JpegDecode.lean:99 | 1 | FAIL | structure param/result |
| `JpegDecode.Frame.mk` | JpegDecode.lean:92 | 1 | FAIL | ctor/projection |
| `JpegDecode.Frame.prog` | JpegDecode.lean:93 | 1 | FAIL | structure param/result |
| `JpegDecode.Frame.vmax` | JpegDecode.lean:98 | 1 | FAIL | structure param/result |
| `JpegDecode.Frame.w` | JpegDecode.lean:94 | 1 | FAIL | structure param/result |
| `JpegDecode.Scan.ah` | JpegDecode.lean:107 | 1 | FAIL | structure param/result |
| `JpegDecode.Scan.comps` | JpegDecode.lean:104 | 1 | FAIL | Array |
| `JpegDecode.Scan.se` | JpegDecode.lean:106 | 1 | FAIL | structure param/result |
| `JpegDecode.Scan.ss` | JpegDecode.lean:105 | 1 | FAIL | structure param/result |
| `Lighting.Light.distant` | Filter/Lighting.lean:36 | 1 | FAIL | ctor/projection |
| `Lighting.Light.point` | Filter/Lighting.lean:37 | 1 | FAIL | ctor/projection |
| `Lighting.Params.b` | Filter/Lighting.lean:50 | 1 | FAIL | structure param/result |
| `Lighting.Params.g` | Filter/Lighting.lean:49 | 1 | FAIL | structure param/result |
| `Lighting.Params.k` | Filter/Lighting.lean:46 | 1 | FAIL | structure param/result |
| `Lighting.Params.mk` | Filter/Lighting.lean:43 | 1 | FAIL | ctor/projection |
| `Lighting.Params.r` | Filter/Lighting.lean:48 | 1 | FAIL | structure param/result |
| `Lighting.Params.se` | Filter/Lighting.lean:47 | 1 | FAIL | structure param/result |
| `Lighting.Params.specular` | Filter/Lighting.lean:44 | 1 | FAIL | structure param/result |
| `Lighting.Params.ss` | Filter/Lighting.lean:45 | 1 | FAIL | structure param/result |
| `Lighting.V3.mk` | Filter/Lighting.lean:189 | 1 | NOOUT | no verdict |
| `Lighting.V3.x` | Filter/Lighting.lean:190 | 1 | FAIL | recursion |
| `Lighting.V3.y` | Filter/Lighting.lean:191 | 1 | FAIL | recursion |
| `Marker.MarkerCtx.fill` | Marker.lean:342 | 1 | NOOUT | no verdict |
| `Marker.MarkerCtx.fillSlot` | Marker.lean:343 | 1 | NOOUT | no verdict |
| `Marker.MarkerCtx.mk` | Marker.lean:341 | 1 | NOOUT | no verdict |
| `Marker.MarkerCtx.stroke` | Marker.lean:344 | 1 | NOOUT | no verdict |
| `Marker.Seg.lineTo` | Marker.lean:130 | 1 | NOOUT | no verdict |
| `Marker.Seg.moveTo` | Marker.lean:129 | 1 | NOOUT | no verdict |
| `Mask.Step.entry` | Mask.lean:40 | 1 | FAIL | structure param/result |
| `Mask.Step.mk` | Mask.lean:39 | 1 | FAIL | ctor/projection |
| `Mask.Step.region` | Mask.lean:41 | 1 | FAIL | structure param/result |
| `Mat.a` | Geom.lean:62 | 1 | FAIL | Int/Fx |
| `Mat.b` | Geom.lean:63 | 1 | FAIL | Int/Fx |
| `Mat.c` | Geom.lean:64 | 1 | FAIL | Int/Fx |
| `Mat.d` | Geom.lean:65 | 1 | FAIL | Int/Fx |
| `Mat.e` | Geom.lean:66 | 1 | FAIL | Int/Fx |
| `Mat.mk` | Geom.lean:61 | 1 | FAIL | ctor/projection |
| `Pat.Defs.buckets` | Pattern.lean:129 | 1 | FAIL | Array |
| `Pat.Defs.defs` | Pattern.lean:128 | 1 | FAIL | Array |
| `Pat.Defs.mk` | Pattern.lean:127 | 1 | FAIL | ctor/projection |
| `Pat.RawDef.hasTransform` | Pattern.lean:75 | 1 | FAIL | ctor/projection |
| `Pat.RawDef.id` | Pattern.lean:64 | 1 | FAIL | ctor/projection |
| `Pat.RawDef.mk` | Pattern.lean:63 | 1 | FAIL | ctor/projection |
| `Pat.RawDef.width` | Pattern.lean:78 | 1 | FAIL | Option/tuple |
| `Pat.RawDef.x` | Pattern.lean:76 | 1 | FAIL | Option/tuple |
| `Pat.RawDef.y` | Pattern.lean:77 | 1 | FAIL | Option/tuple |
| `Pat.Resolved.alignX` | Pattern.lean:118 | 1 | FAIL | structure param/result |
| `Pat.Resolved.alignY` | Pattern.lean:119 | 1 | FAIL | structure param/result |
| `Pat.Resolved.contentOBB` | Pattern.lean:111 | 1 | FAIL | structure param/result |
| `Pat.Resolved.h` | Pattern.lean:116 | 1 | FAIL | Int/Fx |
| `Pat.Resolved.oBB` | Pattern.lean:110 | 1 | FAIL | structure param/result |
| `Pat.Resolved.slice` | Pattern.lean:120 | 1 | FAIL | structure param/result |
| `Pat.Resolved.transform` | Pattern.lean:112 | 1 | FAIL | Int/Fx |
| `Pat.Resolved.valid` | Pattern.lean:109 | 1 | FAIL | structure param/result |
| `Pat.Resolved.viewBox` | Pattern.lean:117 | 1 | FAIL | Int/Fx |
| `Pat.Resolved.w` | Pattern.lean:115 | 1 | FAIL | Int/Fx |
| `Pat.Resolved.x` | Pattern.lean:113 | 1 | FAIL | Int/Fx |
| `Pat.Resolved.y` | Pattern.lean:114 | 1 | FAIL | Int/Fx |
| `Pat.Rt.cv` | PatternRender.lean:72 | 1 | FAIL | structure param/result |
| `Pat.Rt.mk` | PatternRender.lean:69 | 1 | FAIL | ctor/projection |
| `Pat.Rt.px` | PatternRender.lean:73 | 1 | FAIL | structure param/result |
| `Pat.Rt.tileH` | PatternRender.lean:71 | 1 | FAIL | structure param/result |
| `Pat.Rt.tileW` | PatternRender.lean:70 | 1 | FAIL | structure param/result |
| `PathCmd.cubicTo` | Geom.lean:151 | 1 | FAIL | ctor/projection |
| `PathCmd.lineTo` | Geom.lean:150 | 1 | FAIL | ctor/projection |
| `PathCmd.moveTo` | Geom.lean:149 | 1 | FAIL | ctor/projection |
| `PngDecode.Fmt.ctype` | PngDecode.lean:178 | 1 | FAIL | recursion |
| `PngDecode.Fmt.depth` | PngDecode.lean:179 | 1 | FAIL | recursion |
| `PngDecode.Fmt.key` | PngDecode.lean:180 | 1 | FAIL | recursion |
| `PngDecode.Fmt.mk` | PngDecode.lean:177 | 1 | FAIL | ctor/projection |
| `PngDecode.Hdr.ctype` | PngDecode.lean:47 | 1 | FAIL | recursion |
| `PngDecode.Hdr.depth` | PngDecode.lean:46 | 1 | FAIL | recursion |
| `PngDecode.Hdr.h` | PngDecode.lean:45 | 1 | FAIL | recursion |
| `PngDecode.Hdr.mk` | PngDecode.lean:43 | 1 | FAIL | ctor/projection |
| `PngDecode.Hdr.w` | PngDecode.lean:44 | 1 | FAIL | recursion |
| `PngDecode.Meta.hdr` | PngDecode.lean:71 | 1 | FAIL | structure param/result |
| `PngDecode.Meta.mk` | PngDecode.lean:70 | 1 | FAIL | ctor/projection |
| `PngDecode.Meta.plte` | PngDecode.lean:72 | 1 | FAIL | Array |
| `Poly.mk` | Geom.lean:157 | 1 | FAIL | ctor/projection |
| `Poly.pts` | Geom.lean:158 | 1 | FAIL | Array |
| `Pt.mk` | Geom.lean:12 | 1 | FAIL | ctor/projection |
| `Pt.x` | Geom.lean:13 | 1 | FAIL | Int/Fx |
| `Pt.y` | Geom.lean:14 | 1 | FAIL | Int/Fx |
| `Raster.Mask.mk` | Raster.lean:65 | 1 | FAIL | ctor/projection |
| `Raster.Mask.w` | Raster.lean:68 | 1 | FAIL | structure param/result |
| `Raster.Mask.x0` | Raster.lean:66 | 1 | FAIL | structure param/result |
| `Raster.Mask.y0` | Raster.lean:67 | 1 | FAIL | structure param/result |
| `Render.Clip.mk` | Render.lean:60 | 1 | FAIL | ctor/projection |
| `Render.Clip.vx` | Render.lean:69 | 1 | FAIL | Int/Fx |
| `Render.Clip.x0` | Render.lean:61 | 1 | FAIL | structure param/result |
| `Render.Clip.x1` | Render.lean:63 | 1 | FAIL | structure param/result |
| `Render.Clip.y0` | Render.lean:62 | 1 | FAIL | structure param/result |
| `Render.Layer.cache` | Render.lean:504 | 1 | FAIL | structure param/result |
| `Render.Layer.clip` | Render.lean:481 | 1 | FAIL | structure param/result |
| `Render.Layer.cv` | Render.lean:478 | 1 | FAIL | structure param/result |
| `Render.Layer.fh` | Render.lean:503 | 1 | FAIL | structure param/result |
| `Render.Layer.fts` | Render.lean:500 | 1 | FAIL | Int/Fx |
| `Render.Layer.fw` | Render.lean:502 | 1 | FAIL | structure param/result |
| `Render.Layer.lx` | Render.lean:505 | 1 | FAIL | Int/Fx |
| `Render.Layer.masks` | Render.lean:492 | 1 | FAIL | Array |
| `Render.Layer.mk` | Render.lean:477 | 1 | FAIL | ctor/projection |
| `Render.Layer.opacityQ` | Render.lean:484 | 1 | FAIL | structure param/result |
| `Render.Layer.ox` | Render.lean:479 | 1 | FAIL | structure param/result |
| `Render.Layer.oy` | Render.lean:480 | 1 | FAIL | structure param/result |
| `Render.Layer.root` | Render.lean:501 | 1 | FAIL | Int/Fx |
| `Render.Target.clip` | Render.lean:222 | 1 | FAIL | structure param/result |
| `Render.Target.h` | Render.lean:221 | 1 | FAIL | structure param/result |
| `Render.Target.mk` | Render.lean:219 | 1 | FAIL | ctor/projection |
| `Render.Target.ox` | Render.lean:223 | 1 | FAIL | structure param/result |
| `Render.Target.w` | Render.lean:220 | 1 | FAIL | structure param/result |
| `Rgba.a` | Canvas.lean:20 | 1 | FAIL | recursion |
| `Rgba.b` | Canvas.lean:19 | 1 | FAIL | recursion |
| `Rgba.g` | Canvas.lean:18 | 1 | FAIL | recursion |
| `Rgba.mk` | Canvas.lean:16 | 1 | FAIL | ctor/projection |
| `Rgba.r` | Canvas.lean:17 | 1 | FAIL | recursion |
| `Shape.Builder.feats` | Shape.lean:310 | 1 | FAIL | Array |
| `Shape.Builder.mk` | Shape.lean:309 | 1 | FAIL | ctor/projection |
| `Shape.Builder.pauses` | Shape.lean:311 | 1 | FAIL | Array |
| `Shape.FeatureInfo.flags` | Shape.lean:303 | 1 | FAIL | recursion |
| `Shape.FeatureInfo.maxValue` | Shape.lean:302 | 1 | FAIL | recursion |
| `Shape.FeatureInfo.mk` | Shape.lean:299 | 1 | FAIL | ctor/projection |
| `Shape.FeatureInfo.seq` | Shape.lean:301 | 1 | FAIL | recursion |
| `Shape.FeatureInfo.stageSub` | Shape.lean:304 | 1 | FAIL | recursion |
| `Shape.FeatureInfo.tag` | Shape.lean:300 | 1 | FAIL | recursion |
| `Shape.GInfo.cluster` | Shape.lean:70 | 1 | FAIL | recursion |
| `Shape.GInfo.lig` | Shape.lean:84 | 1 | FAIL | recursion |
| `Shape.GPos.mk` | Shape.lean:96 | 1 | NOOUT | no verdict |
| `Shape.GPos.xAdv` | Shape.lean:97 | 1 | NOOUT | no verdict |
| `Shape.GPos.xOff` | Shape.lean:99 | 1 | NOOUT | no verdict |
| `Shape.GPos.yAdv` | Shape.lean:98 | 1 | NOOUT | no verdict |
| `Shape.Glyph.cluster` | ShapeRun.lean:1066 | 1 | NOOUT | no verdict |
| `Shape.Glyph.gid` | ShapeRun.lean:1065 | 1 | NOOUT | no verdict |
| `Shape.Glyph.mk` | ShapeRun.lean:1064 | 1 | NOOUT | no verdict |
| `Shape.Glyph.xAdv` | ShapeRun.lean:1067 | 1 | FAIL | Int/Fx |
| `Shape.Glyph.xOff` | ShapeRun.lean:1068 | 1 | FAIL | Int/Fx |
| `Shape.Indic.Cfg.abvf` | ShapeRun.lean:719 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.blwf` | ShapeRun.lean:718 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.font` | ShapeRun.lean:714 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.half` | ShapeRun.lean:717 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.init` | ShapeRun.lean:722 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.lay` | ShapeRun.lean:713 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.mk` | ShapeRun.lean:711 | 1 | FAIL | ctor/projection |
| `Shape.Indic.Cfg.oldSpec` | ShapeRun.lean:715 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.plan` | ShapeRun.lean:712 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.pref` | ShapeRun.lean:721 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.pstf` | ShapeRun.lean:720 | 1 | FAIL | structure param/result |
| `Shape.Indic.Cfg.rphf` | ShapeRun.lean:716 | 1 | FAIL | structure param/result |
| `Shape.Indic.Re.alt` | ShapeRun.lean:543 | 1 | FAIL | ctor/projection |
| `Shape.Indic.Re.seq` | ShapeRun.lean:542 | 1 | FAIL | ctor/projection |
| `Shape.Indic.Re.star` | ShapeRun.lean:544 | 1 | NOOUT | no verdict |
| `Shape.Indic.Re.sym` | ShapeRun.lean:541 | 1 | NOOUT | no verdict |
| `Shape.Layout.bs` | Shape.lean:159 | 1 | NOOUT | no verdict |
| `Shape.Layout.classDef` | Shape.lean:162 | 1 | NOOUT | no verdict |
| `Shape.Layout.gpos` | Shape.lean:161 | 1 | NOOUT | no verdict |
| `Shape.Layout.gsub` | Shape.lean:160 | 1 | NOOUT | no verdict |
| `Shape.Layout.markAttach` | Shape.lean:163 | 1 | NOOUT | no verdict |
| `Shape.Layout.mk` | Shape.lean:158 | 1 | NOOUT | no verdict |
| `Shape.LookupMap.autoZwj` | Shape.lean:334 | 1 | NOOUT | no verdict |
| `Shape.LookupMap.autoZwnj` | Shape.lean:333 | 1 | NOOUT | no verdict |
| `Shape.LookupMap.index` | Shape.lean:331 | 1 | NOOUT | no verdict |
| `Shape.LookupMap.mask` | Shape.lean:332 | 1 | NOOUT | no verdict |
| `Shape.LookupMap.mk` | Shape.lean:330 | 1 | NOOUT | no verdict |
| `Shape.Plan.gsub` | Shape.lean:341 | 1 | FAIL | Array |
| `Shape.Plan.masks` | Shape.lean:344 | 1 | FAIL | Array |
| `Shape.Plan.mk` | Shape.lean:340 | 1 | FAIL | ctor/projection |
| `Shape.Rule.ahead` | Shape.lean:947 | 1 | FAIL | Array |
| `Shape.Rule.back` | Shape.lean:945 | 1 | FAIL | Array |
| `Shape.Rule.input` | Shape.lean:946 | 1 | FAIL | Array |
| `Shape.Rule.mk` | Shape.lean:944 | 1 | FAIL | ctor/projection |
| `Shape.St.autoZwj` | Shape.lean:488 | 1 | FAIL | structure param/result |
| `Shape.St.autoZwnj` | Shape.lean:489 | 1 | FAIL | structure param/result |
| `Shape.St.haveOutput` | Shape.lean:481 | 1 | FAIL | structure param/result |
| `Shape.St.idx` | Shape.lean:480 | 1 | FAIL | structure param/result |
| `Shape.St.info` | Shape.lean:477 | 1 | FAIL | Array |
| `Shape.St.isGpos` | Shape.lean:476 | 1 | FAIL | structure param/result |
| `Shape.St.lay` | Shape.lean:475 | 1 | FAIL | structure param/result |
| `Shape.St.lookupMask` | Shape.lean:486 | 1 | FAIL | structure param/result |
| `Shape.St.lookupProps` | Shape.lean:487 | 1 | FAIL | structure param/result |
| `Shape.St.maxLen` | Shape.lean:484 | 1 | FAIL | structure param/result |
| `Shape.St.mk` | Shape.lean:474 | 1 | FAIL | ctor/projection |
| `Shape.St.ok` | Shape.lean:482 | 1 | FAIL | structure param/result |
| `Shape.St.ops` | Shape.lean:483 | 1 | FAIL | structure param/result |
| `Shape.St.out` | Shape.lean:478 | 1 | FAIL | Array |
| `Shape.St.perSyl` | Shape.lean:490 | 1 | FAIL | structure param/result |
| `Shape.St.pos` | Shape.lean:479 | 1 | FAIL | Array |
| `Shape.St.serial` | Shape.lean:485 | 1 | FAIL | structure param/result |
| `ShapeText.Cache.fonts` | ShapeText.lean:52 | 1 | NOOUT | no verdict |
| `ShapeText.Cache.mk` | ShapeText.lean:51 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.byteIdx` | ShapeText.lean:43 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.clusterLen` | ShapeText.lean:44 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.dx` | ShapeText.lean:45 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.dy` | ShapeText.lean:46 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.font` | ShapeText.lean:41 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.gid` | ShapeText.lean:42 | 1 | NOOUT | no verdict |
| `ShapeText.SGlyph.mk` | ShapeText.lean:40 | 1 | FAIL | ctor/projection |
| `StrokeStyle.cap` | Geom.lean:488 | 1 | FAIL | structure param/result |
| `StrokeStyle.mk` | Geom.lean:486 | 1 | FAIL | ctor/projection |
| `StrokeStyle.width` | Geom.lean:487 | 1 | FAIL | Int/Fx |
| `Svg.ClipChild.cmds` | Svg.lean:372 | 1 | FAIL | Array |
| `Svg.ClipChild.evenOdd` | Svg.lean:373 | 1 | FAIL | structure param/result |
| `Svg.ClipChild.mk` | Svg.lean:371 | 1 | FAIL | ctor/projection |
| `Svg.ClipEntry.mk` | Svg.lean:387 | 1 | FAIL | ctor/projection |
| `Svg.ClipEntry.selfClip` | Svg.lean:400 | 1 | FAIL | ctor/projection |
| `Svg.ClipEntry.selfClipId` | Svg.lean:399 | 1 | FAIL | ctor/projection |
| `Svg.ClipMode.clip` | Svg.lean:3667 | 1 | FAIL | ctor/projection |
| `Svg.ClipUse.ctm` | Svg.lean:423 | 1 | FAIL | Int/Fx |
| `Svg.ClipUse.entry` | Svg.lean:422 | 1 | FAIL | ctor/projection |
| `Svg.ClipUse.id` | Svg.lean:421 | 1 | FAIL | ctor/projection |
| `Svg.ClipUse.mk` | Svg.lean:420 | 1 | FAIL | ctor/projection |
| `Svg.CtxUse.ctm` | Svg.lean:411 | 1 | FAIL | Int/Fx |
| `Svg.CtxUse.mk` | Svg.lean:410 | 1 | FAIL | ctor/projection |
| `Svg.DefsScan.mk` | Svg.lean:2860 | 1 | FAIL | ctor/projection |
| `Svg.DefsScan.pctRef` | Svg.lean:2866 | 1 | FAIL | structure param/result |
| `Svg.Doc.clips` | Svg.lean:602 | 1 | FAIL | Array |
| `Svg.Doc.masks` | Svg.lean:605 | 1 | FAIL | Array |
| `Svg.Doc.mk` | Svg.lean:598 | 1 | FAIL | ctor/projection |
| `Svg.Doc.patterns` | Svg.lean:618 | 1 | FAIL | structure param/result |
| `Svg.Doc.root` | Svg.lean:599 | 1 | FAIL | structure param/result |
| `Svg.Frame.mk` | Svg.lean:3700 | 1 | FAIL | ctor/projection |
| `Svg.Frame.sbox` | Svg.lean:3736 | 1 | FAIL | Option/tuple |
| `Svg.GroupInfo.blend` | Svg.lean:460 | 1 | FAIL | structure param/result |
| `Svg.GroupInfo.filters` | Svg.lean:475 | 1 | FAIL | Array |
| `Svg.GroupInfo.opacity` | Svg.lean:459 | 1 | FAIL | structure param/result |
| `Svg.MarkerEntry.alignNone` | Svg.lean:560 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.alignX` | Svg.lean:561 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.alignY` | Svg.lean:562 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.height` | Svg.lean:554 | 1 | FAIL | Int/Fx |
| `Svg.MarkerEntry.id` | Svg.lean:549 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.mk` | Svg.lean:548 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.refX` | Svg.lean:550 | 1 | FAIL | Int/Fx |
| `Svg.MarkerEntry.slice` | Svg.lean:563 | 1 | FAIL | ctor/projection |
| `Svg.MarkerEntry.width` | Svg.lean:553 | 1 | FAIL | Int/Fx |
| `Svg.MaskEntry.contentBBox` | Svg.lean:505 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.id` | Svg.lean:503 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.linear` | Svg.lean:508 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.mk` | Svg.lean:502 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.nodes` | Svg.lean:518 | 1 | FAIL | Array |
| `Svg.MaskEntry.pctH` | Svg.lean:515 | 1 | FAIL | Int/Fx |
| `Svg.MaskEntry.pctW` | Svg.lean:514 | 1 | FAIL | Int/Fx |
| `Svg.MaskEntry.selfMask` | Svg.lean:517 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.selfMaskId` | Svg.lean:516 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.userUnits` | Svg.lean:504 | 1 | FAIL | ctor/projection |
| `Svg.MaskEntry.w` | Svg.lean:511 | 1 | FAIL | Option/tuple |
| `Svg.MaskEntry.x` | Svg.lean:509 | 1 | FAIL | Option/tuple |
| `Svg.MaskEntry.y` | Svg.lean:510 | 1 | FAIL | Option/tuple |
| `Svg.MaskLink.self_` | Svg.lean:3778 | 1 | FAIL | ctor/projection |
| `Svg.MaskUse.ctm` | Svg.lean:526 | 1 | FAIL | Int/Fx |
| `Svg.MaskUse.entry` | Svg.lean:525 | 1 | FAIL | ctor/projection |
| `Svg.MaskUse.id` | Svg.lean:524 | 1 | FAIL | ctor/projection |
| `Svg.MaskUse.mk` | Svg.lean:523 | 1 | FAIL | ctor/projection |
| `Svg.Node.shape` | Svg.lean:493 | 1 | FAIL | ctor/projection |
| `Svg.Paint.solid` | Svg.lean:41 | 1 | FAIL | ctor/projection |
| `Svg.PaintFallback.color` | Svg.lean:917 | 1 | FAIL | ctor/projection |
| `Svg.RootInfo.height` | Svg.lean:444 | 1 | FAIL | Int/Fx |
| `Svg.RootInfo.width` | Svg.lean:443 | 1 | FAIL | Int/Fx |
| `Svg.Shape.cmds` | Svg.lean:308 | 1 | FAIL | Array |
| `Svg.Shape.mk` | Svg.lean:307 | 1 | FAIL | ctor/projection |
| `Svg.Style.cap` | Svg.lean:82 | 1 | FAIL | structure param/result |
| `Svg.Style.ctxFill` | Svg.lean:270 | 1 | FAIL | structure param/result |
| `Svg.Style.dashes` | Svg.lean:86 | 1 | FAIL | Array |
| `Svg.Style.dominantBaseline` | Svg.lean:205 | 1 | FAIL | structure param/result |
| `Svg.Style.evenOdd` | Svg.lean:78 | 1 | FAIL | structure param/result |
| `Svg.Style.fill` | Svg.lean:76 | 1 | FAIL | structure param/result |
| `Svg.Style.fillCtx` | Svg.lean:278 | 1 | FAIL | structure param/result |
| `Svg.Style.fillCtxKind` | Svg.lean:286 | 1 | FAIL | structure param/result |
| `Svg.Style.fillOpacity` | Svg.lean:77 | 1 | FAIL | structure param/result |
| `Svg.Style.fontStretch` | Svg.lean:179 | 1 | FAIL | structure param/result |
| `Svg.Style.isolate` | Svg.lean:109 | 1 | FAIL | structure param/result |
| `Svg.Style.join` | Svg.lean:83 | 1 | FAIL | structure param/result |
| `Svg.Style.letterSpacing` | Svg.lean:180 | 1 | FAIL | Int/Fx |
| `Svg.Style.markerMidId` | Svg.lean:300 | 1 | FAIL | ctor/projection |
| `Svg.Style.markerStartId` | Svg.lean:299 | 1 | FAIL | ctor/projection |
| `Svg.Style.mk` | Svg.lean:75 | 1 | FAIL | ctor/projection |
| `Svg.Style.originDx` | Svg.lean:143 | 1 | FAIL | Int/Fx |
| `Svg.Style.ownOverline` | Svg.lean:231 | 1 | FAIL | structure param/result |
| `Svg.Style.ownTextLength` | Svg.lean:238 | 1 | FAIL | Int/Fx |
| `Svg.Style.ownUnderline` | Svg.lean:230 | 1 | FAIL | structure param/result |
| `Svg.Style.patterns` | Svg.lean:156 | 1 | FAIL | structure param/result |
| `Svg.Style.pctRefW` | Svg.lean:137 | 1 | FAIL | Int/Fx |
| `Svg.Style.stroke` | Svg.lean:79 | 1 | FAIL | structure param/result |
| `Svg.Style.strokeOpacity` | Svg.lean:80 | 1 | FAIL | structure param/result |
| `Svg.Style.strokeWidth` | Svg.lean:81 | 1 | FAIL | Int/Fx |
| `Svg.Style.textKerning` | Svg.lean:189 | 1 | FAIL | structure param/result |
| `Svg.SubCfg.layerDepth` | Svg.lean:3882 | 1 | FAIL | recursion |
| `Svg.SubCfg.mk` | Svg.lean:3881 | 1 | FAIL | ctor/projection |
| `SvgImage.Entry.mk` | SvgImage.lean:74 | 1 | FAIL | ctor/projection |
| `SvgImage.Entry.w` | SvgImage.lean:82 | 1 | FAIL | Int/Fx |
| `SvgImage.Entry.x` | SvgImage.lean:80 | 1 | FAIL | Int/Fx |
| `SvgImage.Entry.y` | SvgImage.lean:81 | 1 | FAIL | Int/Fx |
| `Text.CharPos.dx` | Text.lean:428 | 1 | FAIL | Int/Fx |
| `Text.CharPos.dy` | Text.lean:429 | 1 | FAIL | Int/Fx |
| `Text.CharPos.mk` | Text.lean:425 | 1 | FAIL | ctor/projection |
| `Text.CharPos.x` | Text.lean:426 | 1 | FAIL | Int/Fx |
| `Text.CharPos.y` | Text.lean:427 | 1 | FAIL | Int/Fx |
| `Text.Cluster.cp` | Text.lean:646 | 1 | FAIL | structure param/result |
| `Text.Cluster.font` | Text.lean:664 | 1 | FAIL | structure param/result |
| `Text.Cluster.mk` | Text.lean:645 | 1 | FAIL | ctor/projection |
| `Text.Cluster.styleIdx` | Text.lean:647 | 1 | FAIL | structure param/result |
| `Text.DecorRun.mk` | Text.lean:575 | 1 | FAIL | ctor/projection |
| `Text.DecorRun.ox` | Text.lean:577 | 1 | FAIL | Int/Fx |
| `Text.DecorRun.oy` | Text.lean:578 | 1 | FAIL | Int/Fx |
| `Text.DecorRun.rot` | Text.lean:579 | 1 | FAIL | Int/Fx |
| `Text.DecorRun.styleIdx` | Text.lean:576 | 1 | FAIL | structure param/result |
| `Text.DecorRun.unitsPerEm` | Text.lean:581 | 1 | FAIL | structure param/result |
| `Text.DecorRun.width` | Text.lean:580 | 1 | FAIL | Int/Fx |
| `Text.ElemPos.dxs` | Text.lean:262 | 1 | FAIL | Array |
| `Text.ElemPos.dys` | Text.lean:263 | 1 | FAIL | Array |
| `Text.ElemPos.mk` | Text.lean:259 | 1 | FAIL | ctor/projection |
| `Text.ElemPos.xs` | Text.lean:260 | 1 | FAIL | Array |
| `Text.ElemPos.ys` | Text.lean:261 | 1 | FAIL | Array |
| `Text.Ev.open_` | Text.lean:276 | 1 | FAIL | ctor/projection |
| `Text.Placed.mk` | Text.lean:293 | 1 | FAIL | ctor/projection |
| `Text.Placed.styleIdx` | Text.lean:294 | 1 | FAIL | structure param/result |
| `Text.SpanProps.baselineShiftPx` | Text.lean:220 | 1 | FAIL | Int/Fx |
| `Text.SpanProps.baselineShiftSub` | Text.lean:221 | 1 | FAIL | structure param/result |
| `Text.SpanProps.dominantBaseline` | Text.lean:214 | 1 | FAIL | structure param/result |
| `Text.SpanProps.family` | Text.lean:202 | 1 | FAIL | structure param/result |
| `Text.SpanProps.kerning` | Text.lean:210 | 1 | FAIL | structure param/result |
| `Text.SpanProps.letterSpacing` | Text.lean:207 | 1 | FAIL | Int/Fx |
| `Text.SpanProps.mk` | Text.lean:191 | 1 | FAIL | ctor/projection |
| `Text.SpanProps.overlineIdx` | Text.lean:230 | 1 | FAIL | structure param/result |
| `Text.SpanProps.overlineSize` | Text.lean:236 | 1 | FAIL | Int/Fx |
| `Text.SpanProps.sizeAdjust` | Text.lean:206 | 1 | FAIL | Int/Fx |
| `Text.SpanProps.underlineIdx` | Text.lean:229 | 1 | FAIL | structure param/result |
| `Text.SpanProps.underlineSize` | Text.lean:235 | 1 | FAIL | Int/Fx |
| `Text.SpanProps.weight` | Text.lean:195 | 1 | FAIL | structure param/result |
| `Text.dropFirst` | Text.lean:355 | 1 | FAIL | Array |
| `Text.dropLast` | Text.lean:356 | 1 | FAIL | Array |
| `Text.firstIs` | Text.lean:357 | 1 | FAIL | Array |
| `Text.lastIs` | Text.lean:358 | 1 | FAIL | Array |
| `TextPath.Cub.mk` | TextPath.lean:40 | 1 | FAIL | ctor/projection |
| `TextPath.Cub.p0` | TextPath.lean:41 | 1 | FAIL | Int/Fx |
| `TextPath.Cub.p1` | TextPath.lean:42 | 1 | FAIL | Int/Fx |
| `TextPath.Cub.p2` | TextPath.lean:43 | 1 | FAIL | Int/Fx |
| `TextPath.Normal.cos` | TextPath.lean:229 | 1 | FAIL | Int/Fx |
| `TextPath.Normal.mk` | TextPath.lean:226 | 1 | FAIL | ctor/projection |
| `TextPath.Normal.x` | TextPath.lean:227 | 1 | FAIL | Int/Fx |
| `TextPath.Normal.y` | TextPath.lean:228 | 1 | FAIL | Int/Fx |
| `TextPath.Seg.c` | TextPath.lean:92 | 1 | FAIL | structure param/result |
| `TextPath.Seg.mk` | TextPath.lean:91 | 1 | FAIL | ctor/projection |
| `TextPath.Seg.n` | TextPath.lean:93 | 1 | FAIL | structure param/result |
| `TextPath.Seg.pts` | TextPath.lean:94 | 1 | FAIL | Array |
| `TextPath.Table.mk` | TextPath.lean:102 | 1 | FAIL | ctor/projection |
| `Turbulence.Axis.b0` | Filter/Turbulence.lean:192 | 1 | FAIL | Array |
| `Turbulence.Axis.b1` | Filter/Turbulence.lean:193 | 1 | FAIL | Array |
| `Turbulence.Axis.mk` | Filter/Turbulence.lean:191 | 1 | FAIL | ctor/projection |
| `Turbulence.Axis.r0` | Filter/Turbulence.lean:194 | 1 | FAIL | Array |
| `Turbulence.Params.fxD` | Filter/Turbulence.lean:43 | 1 | FAIL | structure param/result |
| `Turbulence.Params.fxN` | Filter/Turbulence.lean:42 | 1 | FAIL | structure param/result |
| `Turbulence.Params.fyD` | Filter/Turbulence.lean:45 | 1 | FAIL | structure param/result |
| `Turbulence.Params.fyN` | Filter/Turbulence.lean:44 | 1 | FAIL | structure param/result |
| `Turbulence.Params.mk` | Filter/Turbulence.lean:41 | 1 | FAIL | ctor/projection |
| `Turbulence.Params.octaves` | Filter/Turbulence.lean:46 | 1 | FAIL | structure param/result |
| `Turbulence.Params.seed` | Filter/Turbulence.lean:47 | 1 | FAIL | Int/Fx |
| `Turbulence.Params.stitch` | Filter/Turbulence.lean:48 | 1 | FAIL | structure param/result |
| `Units.Metrics.cap` | Units.lean:48 | 1 | FAIL | Int/Fx |
| `Units.Metrics.descent` | Units.lean:52 | 1 | FAIL | Int/Fx |
| `Units.Metrics.mk` | Units.lean:40 | 1 | FAIL | ctor/projection |
| `Units.Metrics.xHeight` | Units.lean:49 | 1 | FAIL | Int/Fx |
| `Units.RootLen.mk` | Units.lean:33 | 1 | FAIL | ctor/projection |
| `Units.RootLen.size` | Units.lean:34 | 1 | FAIL | Int/Fx |
| `Units.RootLen.vpW` | Units.lean:35 | 1 | FAIL | Int/Fx |
| `Use.Ctx.mk` | Use.lean:163 | 1 | NOOUT | no verdict |
| `Use.St.clipPaths` | Use.lean:179 | 1 | NOOUT | no verdict |
| `Use.St.elems` | Use.lean:173 | 1 | NOOUT | no verdict |
| `Use.St.mk` | Use.lean:171 | 1 | FAIL | ctor/projection |
| `Use.St.out` | Use.lean:172 | 1 | FAIL | Array |
| `Use.St.work` | Use.lean:174 | 1 | FAIL | structure param/result |
| `Viewport.AspectRatio.align` | Viewport.lean:28 | 1 | FAIL | Option/tuple |
| `Viewport.AspectRatio.mk` | Viewport.lean:27 | 1 | FAIL | ctor/projection |
| `Xml.Attr.mk` | Xml.lean:36 | 1 | FAIL | ctor/projection |
| `Xml.Attr.name` | Xml.lean:37 | 1 | FAIL | ctor/projection |
| `Xml.Scoped.binds` | Xml.lean:86 | 1 | FAIL | String/Format/Char |
| `Xml.Scoped.html` | Xml.lean:90 | 1 | FAIL | structure param/result |
| `Xml.Scoped.mk` | Xml.lean:85 | 1 | FAIL | ctor/projection |
| `Xml.Scoped.name` | Xml.lean:87 | 1 | FAIL | ctor/projection |
| `Bidi.instBEqCls.beq` | Bidi.lean:63 | 2 | FAIL | structure param/result |
| `Css.Selector.mk` | Css.lean:80 | 2 | FAIL | ctor/projection |
| `Css.instReprCombinator.repr` | Css.lean:71 | 2 | FAIL | String/Format/Char |
| `F32.neg` | Canvas.lean:466 | 2 | FAIL | step proof |
| `FeImage.Job.uh` | Filter/ImageRender.lean:31 | 2 | FAIL | Int/Fx |
| `Filter.ElemCtx.bbox` | Filter.lean:859 | 2 | FAIL | Option/tuple |
| `Filter.ElemCtx.fontSize` | Filter.lean:862 | 2 | FAIL | Int/Fx |
| `Filter.ElemCtx.mk` | Filter.lean:857 | 2 | FAIL | ctor/projection |
| `Filter.Parsers.opOne` | Filter.lean:306 | 2 | FAIL | structure param/result |
| `Filter.Prim.mk` | Filter.lean:234 | 2 | FAIL | ctor/projection |
| `Filter.Prim.sub` | Filter.lean:236 | 2 | FAIL | structure param/result |
| `Filter.RawFilter.prims` | Filter.lean:291 | 2 | FAIL | Array |
| `Filter.instReprMorphOp.repr` | Filter/Morphology.lean:35 | 2 | FAIL | String/Format/Char |
| `FilterFrame.Back.fwd` | FilterFrame.lean:45 | 2 | FAIL | Int/Fx |
| `FilterFrame.Back.y0` | FilterFrame.lean:43 | 2 | FAIL | Int/Fx |
| `FilterFrame.Plan.fts` | FilterFrame.lean:56 | 2 | FAIL | Int/Fx |
| `FilterFrame.Plan.h` | FilterFrame.lean:54 | 2 | FAIL | structure param/result |
| `FilterFrame.chan` | FilterFrame.lean:130 | 2 | FAIL | step proof |
| `Font.Tables.os2` | Font.lean:179 | 2 | FAIL | match shape |
| `Font.cmapOff` | Font.lean:76 | 2 | FAIL | structure param/result |
| `Font.descent` | Font.lean:53 | 2 | FAIL | Int/Fx |
| `Font.glyfLen` | Font.lean:74 | 2 | FAIL | structure param/result |
| `Font.hmtxOff` | Font.lean:83 | 2 | FAIL | structure param/result |
| `Font.maxPointsCap` | Font.lean:85 | 2 | FAIL | structure param/result |
| `Font.superscriptOffset` | Font.lean:69 | 2 | FAIL | Int/Fx |
| `ForeignObject.HStyle.color` | ForeignObject.lean:64 | 2 | FAIL | Array |
| `ForeignObject.HStyle.family` | ForeignObject.lean:69 | 2 | FAIL | Array |
| `ForeignObject.Item.br` | ForeignObject.lean:80 | 2 | FAIL | ctor/projection |
| `Grad.Defs.buckets` | Shader.lean:420 | 2 | FAIL | Array |
| `Grad.RawDef.href` | Shader.lean:356 | 2 | FAIL | ctor/projection |
| `Grad.Rt.spread` | Shader.lean:680 | 2 | FAIL | structure param/result |
| `Grad.Shape.linear` | Shader.lean:399 | 2 | FAIL | ctor/projection |
| `Grad.Shape.radial` | Shader.lean:401 | 2 | FAIL | ctor/projection |
| `Image.instReprFmt.repr` | Image.lean:208 | 2 | FAIL | String/Format/Char |
| `Inflate.Huff.tab` | Inflate.lean:37 | 2 | FAIL | Array |
| `Jpeg.Huff.maxcode` | Jpeg/Huffman.lean:46 | 2 | FAIL | Array |
| `Jpeg.Huff.mk` | Jpeg/Huffman.lean:41 | 2 | FAIL | ctor/projection |
| `Jpeg.Huff.vals` | Jpeg/Huffman.lean:49 | 2 | FAIL | Array |
| `JpegDecode.Comp.bh` | JpegDecode.lean:90 | 2 | FAIL | recursion |
| `JpegDecode.Comp.tq` | JpegDecode.lean:87 | 2 | FAIL | recursion |
| `JpegDecode.Frame.mcuy` | JpegDecode.lean:100 | 2 | FAIL | structure param/result |
| `JpegDecode.Scan.mk` | JpegDecode.lean:102 | 2 | FAIL | ctor/projection |
| `Options.mk` | Render.lean:23 | 2 | FAIL | ctor/projection |
| `Options.width` | Render.lean:25 | 2 | FAIL | structure param/result |
| `Options.zoom` | Render.lean:27 | 2 | FAIL | Int/Fx |
| `Pat.RawDef.contentOBB` | Pattern.lean:70 | 2 | FAIL | ctor/projection |
| `Pat.RawDef.oBB` | Pattern.lean:68 | 2 | FAIL | ctor/projection |
| `Pat.hashId` | Pattern.lean:133 | 2 | FAIL | other: frontx: unsupported t |
| `PathCmd.quadTo` | Geom.lean:152 | 2 | FAIL | ctor/projection |
| `PngDecode.Hdr.interlace` | PngDecode.lean:48 | 2 | FAIL | recursion |
| `PngDecode.Meta.trns` | PngDecode.lean:73 | 2 | FAIL | Array |
| `Raster.Mask.h` | Raster.lean:69 | 2 | FAIL | structure param/result |
| `Render.Layer.filters` | Render.lean:498 | 2 | FAIL | Array |
| `Render.Layer.opacity` | Render.lean:482 | 2 | FAIL | structure param/result |
| `Shape.GInfo.cat` | Shape.lean:87 | 2 | FAIL | recursion |
| `Shape.GInfo.cp` | Shape.lean:66 | 2 | FAIL | recursion |
| `Shape.GInfo.gc` | Shape.lean:74 | 2 | FAIL | recursion |
| `Shape.GInfo.gid` | Shape.lean:68 | 2 | FAIL | recursion |
| `Shape.GInfo.gprops` | Shape.lean:82 | 2 | FAIL | recursion |
| `Shape.GInfo.mk` | Shape.lean:64 | 2 | NOOUT | no verdict |
| `Shape.GInfo.syl` | Shape.lean:85 | 2 | NOOUT | no verdict |
| `Shape.GPos.chain` | Shape.lean:102 | 2 | NOOUT | no verdict |
| `Shape.GPos.yOff` | Shape.lean:100 | 2 | NOOUT | no verdict |
| `Shape.Indic.Cfg.virama` | ShapeRun.lean:723 | 2 | FAIL | structure param/result |
| `Shape.Indic.Re.opt` | ShapeRun.lean:545 | 2 | FAIL | ctor/projection |
| `Shape.Plan.gpos` | Shape.lean:342 | 2 | FAIL | Array |
| `Shape.Rule.records` | Shape.lean:948 | 2 | FAIL | Array |
| `Shape.instBEqMatch.beq` | Shape.lean:675 | 2 | FAIL | structure param/result |
| `Shape.instBEqShaper.beq` | ShapeRun.lean:87 | 2 | FAIL | structure param/result |
| `ShapeText.Cache.loaded` | ShapeText.lean:53 | 2 | NOOUT | no verdict |
| `StrokeStyle.join` | Geom.lean:489 | 2 | FAIL | structure param/result |
| `Svg.ClipEntry.id` | Svg.lean:388 | 2 | FAIL | ctor/projection |
| `Svg.ClipEntry.transformValid` | Svg.lean:393 | 2 | FAIL | ctor/projection |
| `Svg.DefsScan.clips` | Svg.lean:2867 | 2 | FAIL | String/Format/Char |
| `Svg.Doc.ctxUses` | Svg.lean:623 | 2 | FAIL | Array |
| `Svg.Doc.nodes` | Svg.lean:600 | 2 | FAIL | Array |
| `Svg.Doc.patternContent` | Svg.lean:619 | 2 | FAIL | Array |
| `Svg.Doc.svgImages` | Svg.lean:621 | 2 | FAIL | Array |
| `Svg.Doc.uses` | Svg.lean:603 | 2 | FAIL | Array |
| `Svg.Frame.bbox` | Svg.lean:3704 | 2 | FAIL | Option/tuple |
| `Svg.Frame.filterAt` | Svg.lean:3728 | 2 | FAIL | structure param/result |
| `Svg.Frame.filterOnly` | Svg.lean:3730 | 2 | FAIL | structure param/result |
| `Svg.Frame.want` | Svg.lean:3709 | 2 | FAIL | structure param/result |
| `Svg.GroupInfo.mk` | Svg.lean:457 | 2 | FAIL | ctor/projection |
| `Svg.GroupInfo.passthrough` | Svg.lean:479 | 2 | FAIL | structure param/result |
| `Svg.MarkerEntry.refY` | Svg.lean:551 | 2 | FAIL | Int/Fx |
| `Svg.MaskEntry.alpha` | Svg.lean:506 | 2 | FAIL | ctor/projection |
| `Svg.MaskEntry.h` | Svg.lean:512 | 2 | FAIL | Option/tuple |
| `Svg.PaintSpec.solid` | Svg.lean:925 | 2 | FAIL | ctor/projection |
| `Svg.RootInfo.viewBox` | Svg.lean:445 | 2 | FAIL | Int/Fx |
| `Svg.SpanLayers.mk` | Svg.lean:3197 | 2 | FAIL | ctor/projection |
| `Svg.SpanLayers.owners` | Svg.lean:3199 | 2 | FAIL | Array |
| `Svg.Style.arcJoins` | Svg.lean:187 | 2 | FAIL | Array |
| `Svg.Style.blend` | Svg.lean:107 | 2 | FAIL | structure param/result |
| `Svg.Style.fontSmallCaps` | Svg.lean:177 | 2 | FAIL | structure param/result |
| `Svg.Style.fontWeight` | Svg.lean:172 | 2 | FAIL | structure param/result |
| `Svg.Style.lang` | Svg.lean:247 | 2 | FAIL | structure param/result |
| `Svg.Style.maskAlpha` | Svg.lean:292 | 2 | FAIL | structure param/result |
| `Svg.Style.miterLimit` | Svg.lean:84 | 2 | FAIL | Int/Fx |
| `Svg.Style.ownBidiOverride` | Svg.lean:243 | 2 | FAIL | structure param/result |
| `Svg.Style.ownLengthAdjustGlyphs` | Svg.lean:239 | 2 | FAIL | structure param/result |
| `Svg.Style.rootFontSize` | Svg.lean:170 | 2 | FAIL | structure param/result |
| `Svg.Style.spacePreserve` | Svg.lean:245 | 2 | FAIL | structure param/result |
| `Svg.Style.strokeCtxKind` | Svg.lean:287 | 2 | FAIL | structure param/result |
| `Svg.Style.textRtl` | Svg.lean:241 | 2 | FAIL | structure param/result |
| `Svg.SubCfg.outSize` | Svg.lean:3887 | 2 | FAIL | match shape |
| `SvgImage.Entry.h` | SvgImage.lean:83 | 2 | FAIL | Int/Fx |
| `SvgImage.Entry.layerDepth` | SvgImage.lean:78 | 2 | FAIL | structure param/result |
| `Text.Cluster.props` | Text.lean:648 | 2 | FAIL | structure param/result |
| `Text.DecorRun.dyUnits` | Text.lean:587 | 2 | FAIL | Int/Fx |
| `Text.SpanProps.italic` | Text.lean:196 | 2 | FAIL | structure param/result |
| `Text.SpanProps.smallCaps` | Text.lean:200 | 2 | FAIL | structure param/result |
| `Text.SpanProps.stretch` | Text.lean:198 | 2 | FAIL | structure param/result |
| `Text.SpanProps.wordSpacing` | Text.lean:208 | 2 | FAIL | Int/Fx |
| `Text.instReprAlignmentBaseline.repr` | Baseline.lean:74 | 2 | FAIL | String/Format/Char |
| `Text.instReprFace.repr` | Text.lean:70 | 2 | FAIL | String/Format/Char |
| `TextPath.Seg.cum` | TextPath.lean:95 | 2 | FAIL | Array |
| `TextPath.Table.segs` | TextPath.lean:103 | 2 | FAIL | Array |
| `Turbulence.Axis.s` | Filter/Turbulence.lean:195 | 2 | FAIL | Array |
| `Units.Metrics.ascent` | Units.lean:50 | 2 | FAIL | Int/Fx |
| `Units.Metrics.ideo` | Units.lean:46 | 2 | FAIL | structure param/result |
| `Units.Metrics.zero` | Units.lean:44 | 2 | FAIL | structure param/result |
| `Use.Ctx.events` | Use.lean:164 | 2 | NOOUT | no verdict |
| `Use.Ctx.target` | Use.lean:169 | 2 | NOOUT | no verdict |
| `Use.St.maxClips` | Use.lean:180 | 2 | FAIL | structure param/result |
| `Xml.Event.open_` | Xml.lean:42 | 2 | FAIL | ctor/projection |
| `Xml.Scoped.attrs` | Xml.lean:91 | 2 | FAIL | Array |
| `Xml.Scoped.foreign` | Xml.lean:88 | 2 | FAIL | structure param/result |
| `BasicShape.Radius.lp` | BasicShape.lean:56 | 3 | FAIL | ctor/projection |
| `BasicShape.instBEqRefBox.beq` | BasicShape.lean:53 | 3 | FAIL | structure param/result |
| `Brotli.Blocks.left` | Brotli.lean:247 | 3 | FAIL | structure param/result |
| `Brotli.Code.syms` | Brotli.lean:65 | 3 | FAIL | Array |
| `Clip.Mask.m` | Clip.lean:91 | 3 | FAIL | Array |
| `Clip.cov16` | Clip.lean:105 | 3 | FAIL | var×var `*` |
| `Clip.cov8` | Clip.lean:102 | 3 | FAIL | step proof |
| `Clip.div255` | Clip.lean:94 | 3 | FAIL | step proof |
| `Css.AttrOp.startsWithDash` | Css.lean:50 | 3 | FAIL | ctor/projection |
| `Css.Component.comp` | Css.lean:77 | 3 | FAIL | ctor/projection |
| `Css.Component.mk` | Css.lean:73 | 3 | FAIL | ctor/projection |
| `Css.Decl.important` | Css.lean:89 | 3 | FAIL | ctor/projection |
| `Css.Rule.sourceOrder` | Css.lean:95 | 3 | FAIL | structure param/result |
| `Css.Selector.valid` | Css.lean:83 | 3 | FAIL | structure param/result |
| `DSeg.tq` | Geom.lean:848 | 3 | FAIL | Int/Fx |
| `F32.mk` | Canvas.lean:383 | 3 | FAIL | step proof |
| `FeImage.Spec.aspect` | Filter/Image.lean:50 | 3 | FAIL | structure param/result |
| `FeImage.Spec.pre` | Filter/Image.lean:56 | 3 | FAIL | Option/tuple |
| `FeImage.Spec.quality` | Filter/Image.lean:53 | 3 | FAIL | structure param/result |
| `Filter.Kind.displacementMap` | Filter.lean:212 | 3 | FAIL | ctor/projection |
| `Filter.Len.pct` | Filter.lean:428 | 3 | FAIL | ctor/projection |
| `Filter.Prim.kind` | Filter.lean:239 | 3 | FAIL | structure param/result |
| `Filter.RawFilter.hasChildren` | Filter.lean:293 | 3 | FAIL | ctor/projection |
| `Filter.RawPrim.children` | Filter.lean:285 | 3 | FAIL | String/Format/Char |
| `FilterApply.Img.lin` | FilterApply.lean:112 | 3 | FAIL | structure param/result |
| `FilterFrame.Plan.back` | FilterFrame.lean:59 | 3 | FAIL | structure param/result |
| `Font.ascent` | Font.lean:50 | 3 | FAIL | Int/Fx |
| `Font.capHeight` | Font.lean:63 | 3 | FAIL | Int/Fx |
| `Font.cmapFormat` | Font.lean:78 | 3 | FAIL | structure param/result |
| `Font.gposKernSubtables` | Font.lean:91 | 3 | FAIL | Array |
| `Font.kernNPairs` | Font.lean:88 | 3 | FAIL | structure param/result |
| `Font.subscriptOffset` | Font.lean:66 | 3 | FAIL | Int/Fx |
| `Font.underlinePosition` | Font.lean:94 | 3 | FAIL | Int/Fx |
| `ForeignObject.HStyle.align` | ForeignObject.lean:71 | 3 | FAIL | structure param/result |
| `ForeignObject.Line.st` | ForeignObject.lean:254 | 3 | FAIL | structure param/result |
| `Fx.clamp` | Fixed.lean:27 | 3 | FAIL | Int/Fx |
| `Fx.max` | Fixed.lean:43 | 3 | FAIL | Int/Fx |
| `Grad.Axis.eL` | Shader.lean:662 | 3 | FAIL | structure param/result |
| `Grad.Axis.split` | Shader.lean:665 | 3 | FAIL | Int/Fx |
| `Grad.Built.solid` | Shader.lean:882 | 3 | FAIL | ctor/projection |
| `Grad.Defs.ids` | Shader.lean:422 | 3 | FAIL | String/Format/Char |
| `Grad.PctRef.h` | Shader.lean:507 | 3 | FAIL | Int/Fx |
| `Grad.RtStop.a` | Shader.lean:622 | 3 | FAIL | recursion |
| `Grad.RtStop.den` | Shader.lean:625 | 3 | FAIL | recursion |
| `Grad.RtStop.mk` | Shader.lean:615 | 3 | FAIL | ctor/projection |
| `Grad.hashId` | Shader.lean:425 | 3 | FAIL | other: frontx: unsupported t |
| `Image.Pix.px` | Image.lean:232 | 3 | FAIL | Array |
| `Image.Placed.quality` | Image.lean:304 | 3 | FAIL | structure param/result |
| `Jpeg.Huff.lookup` | Jpeg/Huffman.lean:43 | 3 | FAIL | Array |
| `Jpeg.pow2` | Jpeg/Huffman.lean:22 | 3 | FAIL | step proof |
| `Lighting.V3.z` | Filter/Lighting.lean:192 | 3 | FAIL | recursion |
| `Lighting.sq` | Filter/Lighting.lean:301 | 3 | NOOUT | no verdict |
| `Marker.MarkerCtx.strokeSlot` | Marker.lean:345 | 3 | NOOUT | no verdict |
| `Mat.linInRange` | Geom.lean:81 | 3 | FAIL | Int/Fx |
| `Pat.Defs.ids` | Pattern.lean:130 | 3 | FAIL | String/Format/Char |
| `Pat.RawDef.hadChildren` | Pattern.lean:90 | 3 | FAIL | ctor/projection |
| `Pat.RawDef.height` | Pattern.lean:79 | 3 | FAIL | Option/tuple |
| `Pat.RawDef.href` | Pattern.lean:65 | 3 | FAIL | ctor/projection |
| `Pat.RawDef.transform` | Pattern.lean:72 | 3 | FAIL | Int/Fx |
| `Pat.Resolved.alignNone` | Pattern.lean:121 | 3 | FAIL | structure param/result |
| `Pat.Resolved.contentSlot` | Pattern.lean:124 | 3 | FAIL | structure param/result |
| `Pat.Rt.bicubic` | PatternRender.lean:78 | 3 | FAIL | structure param/result |
| `Poly.closed` | Geom.lean:159 | 3 | FAIL | structure param/result |
| `Render.Clip.vy` | Render.lean:70 | 3 | FAIL | Int/Fx |
| `Render.Layer.clips` | Render.lean:489 | 3 | FAIL | Array |
| `Render.Layer.ly` | Render.lean:506 | 3 | FAIL | Int/Fx |
| `Render.Target.oy` | Render.lean:224 | 3 | FAIL | structure param/result |
| `Shape.GInfo.ccc` | Shape.lean:76 | 3 | FAIL | recursion |
| `Shape.GInfo.ipos` | Shape.lean:89 | 3 | FAIL | recursion |
| `Shape.GInfo.mask` | Shape.lean:71 | 3 | NOOUT | no verdict |
| `Shape.GInfo.uflags` | Shape.lean:79 | 3 | NOOUT | no verdict |
| `Shape.Glyph.yOff` | ShapeRun.lean:1069 | 3 | FAIL | Int/Fx |
| `Shape.Layout.markSets` | Shape.lean:164 | 3 | NOOUT | no verdict |
| `Shape.Plan.globalMask` | Shape.lean:345 | 3 | FAIL | structure param/result |
| `Shape.Plan.gposScript` | Shape.lean:348 | 3 | FAIL | structure param/result |
| `Shape.St.matchPos` | Shape.lean:491 | 3 | FAIL | Array |
| `Shape.instBEqSkip.beq` | Shape.lean:672 | 3 | FAIL | structure param/result |
| `StrokeStyle.miterLimit` | Geom.lean:491 | 3 | FAIL | Int/Fx |
| `Svg.ClipChild.ctm` | Svg.lean:374 | 3 | FAIL | Int/Fx |
| `Svg.ClipChild.fine` | Svg.lean:384 | 3 | FAIL | structure param/result |
| `Svg.ClipChild.visible` | Svg.lean:377 | 3 | FAIL | structure param/result |
| `Svg.ClipEntry.children` | Svg.lean:401 | 3 | FAIL | Array |
| `Svg.ClipEntry.transform` | Svg.lean:390 | 3 | FAIL | Int/Fx |
| `Svg.ClipUse.bbox` | Svg.lean:424 | 3 | FAIL | Option/tuple |
| `Svg.ClipUse.shape` | Svg.lean:427 | 3 | FAIL | Option/tuple |
| `Svg.DefsScan.markers` | Svg.lean:2872 | 3 | FAIL | String/Format/Char |
| `Svg.DefsScan.masks` | Svg.lean:2869 | 3 | FAIL | String/Format/Char |
| `Svg.DefsScan.patterns` | Svg.lean:2875 | 3 | FAIL | Array |
| `Svg.Doc.markers` | Svg.lean:610 | 3 | FAIL | Array |
| `Svg.Frame.isShapeLeaf` | Svg.lean:3725 | 3 | FAIL | structure param/result |
| `Svg.Frame.maskUse` | Svg.lean:3711 | 3 | FAIL | structure param/result |
| `Svg.Frame.mode` | Svg.lean:3701 | 3 | FAIL | structure param/result |
| `Svg.Frame.useSlot` | Svg.lean:3706 | 3 | FAIL | structure param/result |
| `Svg.Frame.wantS` | Svg.lean:3737 | 3 | FAIL | structure param/result |
| `Svg.GroupInfo.clips` | Svg.lean:468 | 3 | FAIL | Array |
| `Svg.GroupInfo.filterCtm` | Svg.lean:476 | 3 | FAIL | Int/Fx |
| `Svg.MarkerEntry.unitsUser` | Svg.lean:568 | 3 | FAIL | ctor/projection |
| `Svg.MarkerOrient.fixed` | Svg.lean:545 | 3 | FAIL | ctor/projection |
| `Svg.MaskLink.use` | Svg.lean:3779 | 3 | FAIL | ctor/projection |
| `Svg.PaintSpec.url` | Svg.lean:927 | 3 | FAIL | ctor/projection |
| `Svg.RootInfo.mk` | Svg.lean:440 | 3 | FAIL | ctor/projection |
| `Svg.Shape.image` | Svg.lean:318 | 3 | FAIL | Option/tuple |
| `Svg.Shape.markerable` | Svg.lean:315 | 3 | FAIL | structure param/result |
| `Svg.SpanLayers.chains` | Svg.lean:3201 | 3 | FAIL | Array |
| `Svg.Style.clipShapeRaw` | Svg.lean:258 | 3 | FAIL | Array |
| `Svg.Style.ctxStroke` | Svg.lean:271 | 3 | FAIL | structure param/result |
| `Svg.Style.fontAvailable` | Svg.lean:211 | 3 | FAIL | structure param/result |
| `Svg.Style.fontItalic` | Svg.lean:174 | 3 | FAIL | structure param/result |
| `Svg.Style.fontSizeAdjust` | Svg.lean:184 | 3 | FAIL | Int/Fx |
| `Svg.Style.imageRendering` | Svg.lean:304 | 3 | FAIL | structure param/result |
| `Svg.Style.markerCtx` | Svg.lean:283 | 3 | FAIL | structure param/result |
| `Svg.Style.markerEndId` | Svg.lean:301 | 3 | FAIL | ctor/projection |
| `Svg.Style.markersPos` | Svg.lean:100 | 3 | FAIL | structure param/result |
| `Svg.Style.maskRef` | Svg.lean:289 | 3 | FAIL | ctor/projection |
| `Svg.Style.strokeFirst` | Svg.lean:97 | 3 | FAIL | structure param/result |
| `Svg.Style.wordSpacing` | Svg.lean:181 | 3 | FAIL | Int/Fx |
| `Svg.clampHi` | Svg.lean:1136 | 3 | NOOUT | no verdict |
| `SvgImage.Entry.events` | SvgImage.lean:75 | 3 | FAIL | Array |
| `SvgImage.Entry.inner` | SvgImage.lean:85 | 3 | FAIL | Int/Fx |
| `Text.CharPos.rot` | Text.lean:430 | 3 | FAIL | Int/Fx |
| `Text.Cluster.adv` | Text.lean:650 | 3 | FAIL | Int/Fx |
| `Text.Cluster.base` | Text.lean:665 | 3 | FAIL | structure param/result |
| `Text.Cluster.glyphs` | Text.lean:676 | 3 | FAIL | Array |
| `Text.Cluster.sx` | Text.lean:679 | 3 | FAIL | Int/Fx |
| `Text.DecorRun.thicknessUnits` | Text.lean:589 | 3 | FAIL | Int/Fx |
| `Text.Placed.cmds` | Text.lean:295 | 3 | FAIL | Array |
| `Text.SpanProps.anchor` | Text.lean:211 | 3 | FAIL | structure param/result |
| `Text.SpanProps.face` | Text.lean:192 | 3 | FAIL | structure param/result |
| `Text.SpanProps.lengthAdjustGlyphs` | Text.lean:244 | 3 | FAIL | structure param/result |
| `Text.SpanProps.size` | Text.lean:203 | 3 | FAIL | Int/Fx |
| `Text.SpanProps.textLength` | Text.lean:241 | 3 | FAIL | Int/Fx |
| `TextPath.Normal.sin` | TextPath.lean:230 | 3 | FAIL | Int/Fx |
| `TextPath.Seg.s0` | TextPath.lean:97 | 3 | FAIL | Int/Fx |
| `TextPath.Table.total` | TextPath.lean:105 | 3 | FAIL | Int/Fx |
| `TextPath.rdiv` | TextPath.lean:50 | 3 | FAIL | Int/Fx |
| `Turbulence.Params.fractal` | Filter/Turbulence.lean:49 | 3 | FAIL | structure param/result |
| `Turbulence.wrap32` | Filter/Turbulence.lean:64 | 3 | FAIL | Int/Fx |
| `Units.Metrics.lineGap` | Units.lean:53 | 3 | FAIL | Int/Fx |
| `Units.Metrics.upem` | Units.lean:41 | 3 | FAIL | structure param/result |
| `Use.Ctx.endOf` | Use.lean:166 | 3 | NOOUT | no verdict |
| `Use.resolveLen` | Use.lean:91 | 3 | FAIL | Int/Fx |
| `Viewport.AspectRatio.slice` | Viewport.lean:29 | 3 | FAIL | structure param/result |
| `Woff.pushU16` | Woff.lean:53 | 3 | FAIL | Array |
| `BasicShape.Env.pathData` | BasicShape.lean:83 | 4 | FAIL | Array |
| `BasicShape.Geo.rect` | BasicShape.lean:64 | 4 | FAIL | ctor/projection |
| `Bidi.overrideCls` | Bidi.lean:376 | 4 | NOOUT | no verdict |
| `Brotli.setByte` | Brotli.lean:312 | 4 | FAIL | Array |
| `FeImage.cost` | Filter/ImageRender.lean:65 | 4 | FAIL | Array |
| `Filter.Kind.convolveMatrix` | Filter.lean:206 | 4 | FAIL | ctor/projection |
| `Filter.Outcome.filters` | Filter.lean:853 | 4 | FAIL | ctor/projection |
| `Filter.RawPrim.color` | Filter.lean:279 | 4 | FAIL | ctor/projection |
| `FilterFrame.Back.vy` | FilterFrame.lean:48 | 4 | FAIL | Int/Fx |
| `Font.lineGap` | Font.lean:55 | 4 | FAIL | Int/Fx |
| `Font.strByte` | Font.lean:1067 | 4 | FAIL | do-block shape |
| `Font.xHeight` | Font.lean:59 | 4 | FAIL | Int/Fx |
| `ForeignObject.isHtml` | ForeignObject.lean:399 | 4 | FAIL | other: frontx: unsupported B |
| `Fx.hypot` | Fixed.lean:46 | 4 | FAIL | Int/Fx |
| `Fx.inRange` | Fixed.lean:30 | 4 | FAIL | Int/Fx |
| `Grad.Defs.defs` | Shader.lean:416 | 4 | FAIL | Array |
| `Grad.RawDef.fr` | Shader.lean:370 | 4 | FAIL | Option/tuple |
| `Grad.Rt.stops` | Shader.lean:684 | 4 | FAIL | Array |
| `Grad.instReprKind.repr` | Shader.lean:336 | 4 | FAIL | String/Format/Char |
| `Grad.norm2` | Shader.lean:152 | 4 | FAIL | Int/Fx |
| `Grad.recipOf` | Shader.lean:730 | 4 | FAIL | `/` `%` by var |
| `Grad.sqrt16` | Shader.lean:148 | 4 | FAIL | Int/Fx |
| `Image.chans` | Image.lean:420 | 4 | NOOUT | no verdict |
| `Image.clampIx` | Image.lean:405 | 4 | FAIL | Int/Fx |
| `Marker.Seg.cubicTo` | Marker.lean:131 | 4 | NOOUT | no verdict |
| `Mat.clampLin` | Geom.lean:74 | 4 | FAIL | Int/Fx |
| `Oklab.encode` | Oklab.lean:96 | 4 | FAIL | loops other than `for i in [ |
| `Pat.RawDef.aspect` | Pattern.lean:86 | 4 | FAIL | ctor/projection |
| `Pat.RawDef.viewBox` | Pattern.lean:82 | 4 | FAIL | Int/Fx |
| `Pat.Rt.py` | PatternRender.lean:74 | 4 | FAIL | structure param/result |
| `Pat.unpack` | PatternRender.lean:91 | 4 | NOOUT | no verdict |
| `Png.be32` | Png.lean:154 | 4 | FAIL | Array |
| `PngDecode.Fmt.pal` | PngDecode.lean:181 | 4 | FAIL | Array |
| `Raster.toFDot6` | Raster.lean:529 | 4 | FAIL | Int/Fx |
| `Render.Layer.blend` | Render.lean:485 | 4 | FAIL | structure param/result |
| `Shape.Builder.stageSub` | Shape.lean:312 | 4 | FAIL | structure param/result |
| `Shape.FeatureInfo.stagePos` | Shape.lean:305 | 4 | FAIL | recursion |
| `Shape.GInfo.ngid` | Shape.lean:92 | 4 | NOOUT | no verdict |
| `Shape.GPos.atype` | Shape.lean:104 | 4 | NOOUT | no verdict |
| `ShapeText.SGlyph.width` | ShapeText.lean:47 | 4 | FAIL | Int/Fx |
| `StixNonUnicode.lookup` | StixNonUnicode.lean:21 | 4 | FAIL | resource: simp/whnf depth or |
| `Svg.ClipChild.clips` | Svg.lean:380 | 4 | FAIL | Array |
| `Svg.ClipEntry.objectBBox` | Svg.lean:395 | 4 | FAIL | ctor/projection |
| `Svg.Doc.maskUses` | Svg.lean:606 | 4 | FAIL | Array |
| `Svg.Frame.ctxUse` | Svg.lean:3732 | 4 | FAIL | structure param/result |
| `Svg.Frame.maskSlot` | Svg.lean:3714 | 4 | FAIL | structure param/result |
| `Svg.GroupInfo.mask` | Svg.lean:471 | 4 | FAIL | structure param/result |
| `Svg.MarkerEntry.content` | Svg.lean:587 | 4 | FAIL | Array |
| `Svg.MarkerEntry.orient` | Svg.lean:564 | 4 | FAIL | structure param/result |
| `Svg.MaskEntry.filled` | Svg.lean:519 | 4 | FAIL | ctor/projection |
| `Svg.PaintSpec.context` | Svg.lean:930 | 4 | FAIL | ctor/projection |
| `Svg.Style.clipRef` | Svg.lean:254 | 4 | FAIL | ctor/projection |
| `Svg.Style.clips` | Svg.lean:261 | 4 | FAIL | Array |
| `Svg.Style.crisp` | Svg.lean:117 | 4 | FAIL | structure param/result |
| `Svg.Style.ctxSlot` | Svg.lean:274 | 4 | FAIL | structure param/result |
| `Svg.Style.fontFamily` | Svg.lean:214 | 4 | FAIL | structure param/result |
| `Svg.Style.fontFamilyRaw` | Svg.lean:218 | 4 | FAIL | Array |
| `Svg.Style.ownOpacity` | Svg.lean:103 | 4 | FAIL | structure param/result |
| `Svg.Style.strokeCtx` | Svg.lean:279 | 4 | FAIL | structure param/result |
| `Svg.Style.writingMode` | Svg.lean:201 | 4 | FAIL | structure param/result |
| `Svg.SubCfg.nested` | Svg.lean:3883 | 4 | FAIL | recursion |
| `Svg.isShape` | Svg.lean:2569 | 4 | FAIL | do-block shape |
| `Svg.paintOrderPos` | Svg.lean:2051 | 4 | FAIL | Array |
| `Svg.rot90` | Svg.lean:1122 | 4 | FAIL | structure param/result |
| `Synth.skew` | Synth.lean:36 | 4 | FAIL | Int/Fx |
| `Text.Cluster.dropped` | Text.lean:668 | 4 | FAIL | structure param/result |
| `Text.Cluster.natWidth` | Text.lean:660 | 4 | FAIL | Int/Fx |
| `Text.Cluster.off` | Text.lean:672 | 4 | FAIL | structure param/result |
| `Text.ElemPos.rots` | Text.lean:264 | 4 | FAIL | Array |
| `Text.SpanProps.bidiOverride` | Text.lean:251 | 4 | FAIL | structure param/result |
| `Text.SpanProps.lang` | Text.lean:255 | 4 | FAIL | structure param/result |
| `Text.SpanProps.rtl` | Text.lean:247 | 4 | FAIL | structure param/result |
| `Text.SpanProps.throughIdx` | Text.lean:231 | 4 | FAIL | structure param/result |
| `Text.SpanProps.throughSize` | Text.lean:237 | 4 | FAIL | Int/Fx |
| `Text.allSpace` | Text.lean:359 | 4 | FAIL | Array |
| `Turbulence.sat32` | Filter/Turbulence.lean:60 | 4 | FAIL | Int/Fx |
| `Units.RootLen.vpH` | Units.lean:36 | 4 | FAIL | Int/Fx |
| `Use.St.clipN` | Use.lean:175 | 4 | NOOUT | no verdict |
| `Warn.add` | Warn.lean:26 | 4 | FAIL | String/Format/Char |
| `Xml.Attr.value` | Xml.lean:38 | 4 | FAIL | Array |
| `BasicShape.Geo.path` | BasicShape.lean:69 | 5 | FAIL | ctor/projection |
| `BasicShape.Spec.ref` | BasicShape.lean:76 | 5 | FAIL | structure param/result |
| `Bidi.clsOfIndex` | Bidi.lean:65 | 5 | NOOUT | no verdict |
| `Bidi.isIsoInit` | Bidi.lean:75 | 5 | FAIL | structure param/result |
| `Bidi.isNI` | Bidi.lean:80 | 5 | FAIL | structure param/result |
| `Bidi.removedX9` | Bidi.lean:70 | 5 | NOOUT | no verdict |
| `Box.y1` | Geom.lean:336 | 5 | FAIL | Int/Fx |
| `Canvas.px` | Canvas.lean:26 | 5 | FAIL | Array |
| `Css.Compound.firstChild` | Css.lean:59 | 5 | FAIL | ctor/projection |
| `Css.ElemInfo.isFirstChild` | Css.lean:103 | 5 | FAIL | ctor/projection |
| `FeImage.Href.data` | Filter/Image.lean:43 | 5 | FAIL | ctor/projection |
| `Filter.ElemCtx.vbH` | Filter.lean:865 | 5 | FAIL | Int/Fx |
| `Filter.TF.gamma` | Filter.lean:181 | 5 | FAIL | ctor/projection |
| `Filter.Table.ids` | Filter.lean:298 | 5 | FAIL | String/Format/Char |
| `Filter.UrlRes.ok` | Filter.lean:870 | 5 | FAIL | ctor/projection |
| `Filter.mul16` | Filter.lean:466 | 5 | FAIL | Int/Fx |
| `Font.roundDiv14` | Font.lean:131 | 5 | FAIL | Int/Fx |
| `Font.underlineThickness` | Font.lean:97 | 5 | FAIL | Int/Fx |
| `ForeignObject.Item.bgStart` | ForeignObject.lean:82 | 5 | FAIL | ctor/projection |
| `Grad.Aff.f` | Shader.lean:188 | 5 | FAIL | Int/Fx |
| `Grad.Resolved.stops` | Shader.lean:410 | 5 | FAIL | Array |
| `Grad.Rt.ramp` | Shader.lean:699 | 5 | FAIL | Array |
| `Grad.instBEqSpread.beq` | Shader.lean:331 | 5 | FAIL | structure param/result |
| `Grad.mul16` | Shader.lean:136 | 5 | FAIL | Int/Fx |
| `Image.bicFar` | Image.lean:415 | 5 | FAIL | Int/Fx |
| `Image.premulU8` | Image.lean:235 | 5 | FAIL | var×var `*` |
| `Image.round32` | Image.lean:424 | 5 | FAIL | Int/Fx |
| `JpegDecode.Scan.al` | JpegDecode.lean:108 | 5 | FAIL | structure param/result |
| `Lighting.Light.spot` | Filter/Lighting.lean:38 | 5 | FAIL | ctor/projection |
| `Lighting.Params.light` | Filter/Lighting.lean:51 | 5 | FAIL | structure param/result |
| `Mask.Res.chain` | Mask.lean:49 | 5 | FAIL | ctor/projection |
| `Pat.Built.tile` | PatternRender.lean:86 | 5 | FAIL | ctor/projection |
| `Pat.Resolved.mk` | Pattern.lean:104 | 5 | FAIL | ctor/projection |
| `Pat.Rt.alpha8` | PatternRender.lean:81 | 5 | FAIL | structure param/result |
| `Raster.insideW` | Raster.lean:83 | 5 | FAIL | Int/Fx |
| `Render.Clip.y1` | Render.lean:64 | 5 | FAIL | structure param/result |
| `Render.Layer.maskMat` | Render.lean:493 | 5 | FAIL | Int/Fx |
| `Shape.LookupMap.perSyl` | Shape.lean:335 | 5 | NOOUT | no verdict |
| `Shape.nextGlyphs` | Shape.lean:519 | 5 | FAIL | monadic type (Shape.M / Stat |
| `Svg.DefsScan.grads` | Svg.lean:2861 | 5 | FAIL | Array |
| `Svg.Doc.events` | Svg.lean:613 | 5 | FAIL | Array |
| `Svg.MarkerEntry.clipEntryIdx` | Svg.lean:577 | 5 | FAIL | ctor/projection |
| `Svg.MarkerEntry.valid` | Svg.lean:582 | 5 | FAIL | ctor/projection |
| `Svg.MarkerEntry.viewBox` | Svg.lean:555 | 5 | FAIL | Int/Fx |
| `Svg.OriginTok.isHoriz` | Svg.lean:1597 | 5 | FAIL | structure param/result |
| `Svg.OriginTok.isVert` | Svg.lean:1602 | 5 | FAIL | structure param/result |
| `Svg.Style.alignmentBaseline` | Svg.lean:206 | 5 | FAIL | structure param/result |
| `Svg.Style.clipEvenOdd` | Svg.lean:249 | 5 | FAIL | structure param/result |
| `Svg.Style.color` | Svg.lean:126 | 5 | FAIL | structure param/result |
| `Svg.Style.dashOffset` | Svg.lean:87 | 5 | FAIL | Int/Fx |
| `Svg.Style.filterRaw` | Svg.lean:294 | 5 | FAIL | Array |
| `Svg.Style.opacity` | Svg.lean:92 | 5 | FAIL | structure param/result |
| `Svg.Style.ownMat` | Svg.lean:265 | 5 | FAIL | Int/Fx |
| `Svg.Style.pctRefH` | Svg.lean:138 | 5 | FAIL | Int/Fx |
| `Svg.Style.textCrisp` | Svg.lean:121 | 5 | FAIL | structure param/result |
| `Text.DecorRun.size` | Text.lean:582 | 5 | FAIL | Int/Fx |
| `Text.Placed.boldSize` | Text.lean:298 | 5 | FAIL | Int/Fx |
| `Text.SpanProps.alignmentBaseline` | Text.lean:215 | 5 | FAIL | structure param/result |
| `Text.instReprAnchor.repr` | Text.lean:186 | 5 | FAIL | String/Format/Char |
| `Text.roundDivI` | Text.lean:689 | 5 | FAIL | Int/Fx |
| `Turbulence.random` | Filter/Turbulence.lean:94 | 5 | FAIL | Int/Fx |
| `Woff.fitsI16` | Woff.lean:174 | 5 | FAIL | Int/Fx |
| `arcSteps` | Geom.lean:532 | 5 | FAIL | Int/Fx |
| `degToRad16` | Geom.lean:33 | 5 | FAIL | Int/Fx |
| `dropClosingDup` | Geom.lean:727 | 5 | FAIL | Array |
| `instBEqBlendMode.beq` | Canvas.lean:567 | 5 | FAIL | structure param/result |
| `BasicShape.sideDist` | BasicShape.lean:390 | 6 | FAIL | Int/Fx |
| `Bidi.hexDigit` | Bidi.lean:276 | 6 | NOOUT | no verdict |
| `Clip.Res.chain` | Clip.lean:247 | 6 | FAIL | ctor/projection |
| `Filter.Input.ref` | Filter.lean:162 | 6 | FAIL | ctor/projection |
| `FilterApply.roundAwayDiv` | Filter/DisplacementMap.lean:30 | 6 | FAIL | Int/Fx |
| `FilterApply.truncPx` | FilterApply.lean:471 | 6 | FAIL | Int/Fx |
| `Font.data` | Font.lean:103 | 6 | FAIL | Array |
| `Font.numGlyphs` | Font.lean:44 | 6 | FAIL | structure param/result |
| `Font.valueRecordSize` | Font.lean:430 | 6 | FAIL | step proof |
| `FontFace.hexVal` | FontFace.lean:138 | 6 | NOOUT | no verdict |
| `Grad.Built.grad` | Shader.lean:885 | 6 | FAIL | ctor/projection |
| `Image.bicNear` | Image.lean:409 | 6 | FAIL | Int/Fx |
| `Image.hexDigit` | Image.lean:66 | 6 | NOOUT | no verdict |
| `Options.background` | Render.lean:29 | 6 | FAIL | structure param/result |
| `PngDecode.paeth` | PngDecode.lean:142 | 6 | FAIL | step proof |
| `PngDecode.passes` | PngDecode.lean:122 | 6 | FAIL | Array |
| `PngDecode.to8` | PngDecode.lean:225 | 6 | FAIL | `/` `%` by var |
| `Raster.addAlpha` | Raster.lean:88 | 6 | FAIL | Array |
| `Raster.divRound` | Raster.lean:533 | 6 | FAIL | Int/Fx |
| `Shape.Indic.union` | ShapeRun.lean:547 | 6 | NOOUT | no verdict |
| `Shape.St.rtl` | Shape.lean:494 | 6 | FAIL | structure param/result |
| `Svg.ClipEntry.filled` | Svg.lean:404 | 6 | FAIL | ctor/projection |
| `Svg.MarkerEntry.clip` | Svg.lean:571 | 6 | FAIL | ctor/projection |
| `Svg.Paint.gradient` | Svg.lean:42 | 6 | FAIL | ctor/projection |
| `Svg.Shape.style` | Svg.lean:309 | 6 | FAIL | structure param/result |
| `Svg.Style.ctm` | Svg.lean:157 | 6 | FAIL | Int/Fx |
| `Svg.Style.defs` | Svg.lean:150 | 6 | FAIL | structure param/result |
| `Svg.Style.originDy` | Svg.lean:144 | 6 | FAIL | Int/Fx |
| `Svg.Style.ownLineThrough` | Svg.lean:232 | 6 | FAIL | structure param/result |
| `Svg.Style.pctRefSet` | Svg.lean:131 | 6 | FAIL | structure param/result |
| `TextPath.Cub.p3` | TextPath.lean:44 | 6 | FAIL | Int/Fx |
| `Viewport.instReprPos.repr` | Viewport.lean:21 | 6 | FAIL | String/Format/Char |
| `Viewport.posOf` | Viewport.lean:32 | 6 | FAIL | Option/tuple |
| `Woff.pad4` | Woff.lean:63 | 6 | FAIL | Array |
| `instReprCap.repr` | Geom.lean:480 | 6 | FAIL | String/Format/Char |
| `Canvas.div65025` | Canvas.lean:142 | 7 | FAIL | step proof |
| `Css.Compound.valid` | Css.lean:64 | 7 | FAIL | ctor/projection |
| `FeImage.Job.sy` | Filter/ImageRender.lean:23 | 7 | FAIL | Int/Fx |
| `FeImage.ownProp` | Filter/Image.lean:195 | 7 | FAIL | do-block shape |
| `FontFace.Face.coverage` | FontFace.lean:51 | 7 | FAIL | Array |
| `FontFace.addCp` | FontFace.lean:68 | 7 | FAIL | Array |
| `GifDecode.initDict` | GifDecode.lean:81 | 7 | FAIL | Array |
| `Grad.div16` | Shader.lean:141 | 7 | FAIL | Int/Fx |
| `Grad.hypot16` | Shader.lean:156 | 7 | FAIL | Int/Fx |
| `Image.Rt.quality` | Image.lean:356 | 7 | FAIL | structure param/result |
| `Inflate.rev` | Inflate.lean:39 | 7 | FAIL | step proof |
| `Mask.Step.content` | Mask.lean:42 | 7 | FAIL | Int/Fx |
| `Mat.f` | Geom.lean:67 | 7 | FAIL | Int/Fx |
| `Options.viewport` | Render.lean:35 | 7 | FAIL | Int/Fx |
| `Svg.Frame.fine` | Svg.lean:3718 | 7 | FAIL | structure param/result |
| `Svg.GroupInfo.isolate` | Svg.lean:461 | 7 | FAIL | structure param/result |
| `Svg.MarkerEntry.filled` | Svg.lean:591 | 7 | FAIL | ctor/projection |
| `Svg.Style.fontSize` | Svg.lean:163 | 7 | FAIL | Int/Fx |
| `Svg.Style.visible` | Svg.lean:110 | 7 | FAIL | structure param/result |
| `Svg.padChains` | Svg.lean:3217 | 7 | FAIL | Array |
| `Text.Cluster.width` | Text.lean:653 | 7 | FAIL | Int/Fx |
| `Text.Ev.openPath` | Text.lean:277 | 7 | FAIL | ctor/projection |
| `Text.SpanProps.baselineShiftSuper` | Text.lean:222 | 7 | FAIL | structure param/result |
| `Turbulence.toByte` | Filter/Turbulence.lean:245 | 7 | FAIL | do-block shape |
| `Use.fmtFixed` | Use.lean:150 | 7 | FAIL | ctor/projection |
| `Use.isGraphicTarget` | Use.lean:67 | 7 | FAIL | do-block shape |
| `pushRing` | Geom.lean:604 | 7 | FAIL | Array |
| `Filter.CMKind.hueRotate` | Filter.lean:170 | 8 | FAIL | ctor/projection |
| `Filter.CompOp.arith` | Filter.lean:186 | 8 | FAIL | ctor/projection |
| `Font.tailLen` | Font.lean:111 | 8 | FAIL | structure param/result |
| `Font.xAdvanceOffset` | Font.lean:436 | 8 | FAIL | step proof |
| `Grad.RtStop.recip` | Shader.lean:628 | 8 | FAIL | recursion |
| `Grad.stopAlpha8` | Shader.lean:891 | 8 | FAIL | var×var `*` |
| `Pat.opacityQ` | PatternRender.lean:200 | 8 | FAIL | var×var `*` |
| `Svg.CtxUse.bbox` | Svg.lean:412 | 8 | FAIL | Option/tuple |
| `Svg.Node.groupBegin` | Svg.lean:494 | 8 | FAIL | ctor/projection |
| `Svg.OriginTok.len` | Svg.lean:1589 | 8 | FAIL | ctor/projection |
| `Svg.Style.docFaces` | Svg.lean:222 | 8 | FAIL | Array |
| `Svg.mulOpacity` | Svg.lean:1019 | 8 | FAIL | var×var `*` |
| `Svg.resolvePct` | Svg.lean:1456 | 8 | NOOUT | no verdict |
| `Text.ElemPos.hasRot` | Text.lean:268 | 8 | FAIL | structure param/result |
| `TextPath.accuracyFor` | TextPath.lean:261 | 8 | FAIL | Int/Fx |
| `TextPath.chord` | TextPath.lean:83 | 8 | FAIL | Int/Fx |
| `Use.divRound` | Use.lean:94 | 8 | FAIL | Int/Fx |
| `Use.isDefLike` | Use.lean:74 | 8 | FAIL | do-block shape |
| `Canvas.div255` | Canvas.lean:31 | 9 | FAIL | step proof |
| `Canvas.premul` | Canvas.lean:40 | 9 | FAIL | var×var `*` |
| `Canvas.unpremul` | Canvas.lean:49 | 9 | FAIL | `/` `%` by var |
| `FamilyMatch.generic` | FamilyMatch.lean:93 | 9 | FAIL | do-block shape |
| `Lighting.mulQ` | Filter/Lighting.lean:292 | 9 | FAIL | var×var `*` |
| `Marker.dirUnit16` | Marker.lean:86 | 9 | FAIL | Int/Fx |
| `Mask.coord` | Mask.lean:54 | 9 | FAIL | Int/Fx |
| `Png.blockHeader` | Png.lean:171 | 9 | FAIL | Array |
| `Png.crcAdvance` | Png.lean:34 | 9 | FAIL | Array |
| `Png.zlibLen` | Png.lean:162 | 9 | FAIL | var×var `*` |
| `StixNonUnicode.utf8` | StixNonUnicode.lean:25 | 9 | FAIL | Array |
| `Svg.hueRound` | Svg.lean:812 | 9 | FAIL | Int/Fx |
| `Text.Ev.text` | Text.lean:284 | 9 | FAIL | ctor/projection |
| `Text.roundScale` | Text.lean:592 | 9 | FAIL | Int/Fx |
| `quadDeltaFromLine` | Geom.lean:229 | 9 | FAIL | Int/Fx |
| `Clip.Key.mk` | Clip.lean:253 | 10 | FAIL | ctor/projection |
| `Grad.RawStop.op` | Shader.lean:343 | 10 | FAIL | structure param/result |
| `Grad.cubicAt16` | Shader.lean:242 | 10 | FAIL | Int/Fx |
| `Grad.pickCommon` | Shader.lean:477 | 10 | FAIL | Option/tuple |
| `Render.bandCount` | Render.lean:1002 | 10 | FAIL | step proof |
| `Shape.scriptRtl` | ShapeRun.lean:52 | 10 | FAIL | do-block shape |
| `ShapeText.charOf` | ShapeText.lean:74 | 10 | FAIL | Array |
| `Svg.ClipUse.sbox` | Svg.lean:430 | 10 | FAIL | Option/tuple |
| `Svg.RootInfo.aspect` | Svg.lean:447 | 10 | FAIL | structure param/result |
| `Xml.nsLookup` | Xml.lean:75 | 10 | FAIL | ctor/projection |
| `Filter.decTimes` | Filter.lean:586 | 11 | FAIL | Int/Fx |
| `Grad.Rt.isOpaque` | Shader.lean:688 | 11 | FAIL | structure param/result |
| `Grad.spreadT` | Shader.lean:825 | 11 | FAIL | structure param/result |
| `Pat.RawDef.eventIdx` | Pattern.lean:93 | 11 | FAIL | ctor/projection |
| `Pat.pickCommon` | Pattern.lean:162 | 11 | FAIL | Option/tuple |
| `Svg.ClipMode.markerDef` | Svg.lean:3668 | 11 | FAIL | ctor/projection |
| `Svg.Style.textAnchor` | Svg.lean:190 | 11 | FAIL | structure param/result |
| `Svg.divRound` | Svg.lean:1111 | 11 | FAIL | Int/Fx |
| `SvgImage.layerBox` | SvgImage.lean:118 | 11 | FAIL | Int/Fx |
| `Filter.expSmall` | Filter/Gamma.lean:51 | 12 | FAIL | Int/Fx |
| `Filter.morphCeil` | Filter/Morphology.lean:104 | 12 | FAIL | Int/Fx |
| `Filter.morphScaled` | Filter/Morphology.lean:37 | 12 | FAIL | Int/Fx |
| `FilterApply.iirCoeffs` | FilterApply.lean:385 | 12 | FAIL | var×var `*` |
| `Grad.lerpDown` | Shader.lean:761 | 12 | FAIL | var×var `*` |
| `Raster.Mask.cov` | Raster.lean:71 | 12 | FAIL | Array |
| `Svg.GroupInfo.dropped` | Svg.lean:481 | 12 | FAIL | structure param/result |
| `Woff.tagOf` | Woff.lean:41 | 12 | FAIL | do-block shape |
| `bitLength` | Geom.lean:182 | 12 | FAIL | step proof |
| `len8` | Geom.lean:570 | 12 | FAIL | Int/Fx |
| `Bidi.matchedBracket` | Bidi.lean:335 | 13 | NOOUT | no verdict |
| `Bidi.searchLE` | Bidi.lean:310 | 13 | NOOUT | no verdict |
| `Canvas.pack` | Canvas.lean:58 | 13 | FAIL | step proof |
| `FilterApply.stdDev` | FilterApply.lean:437 | 13 | FAIL | Int/Fx |
| `GifDecode.rowOrder` | GifDecode.lean:146 | 13 | FAIL | Array |
| `Png.crcBytes` | Png.lean:43 | 13 | FAIL | do-block shape |
| `Render.opacityQ` | Render.lean:464 | 13 | FAIL | var×var `*` |
| `Svg.isCssOnlyProp` | Svg.lean:2061 | 13 | FAIL | do-block shape |
| `Text.matchWeight` | Text.lean:72 | 13 | FAIL | structure param/result |
| `Brotli.alphabetBits` | Brotli.lean:108 | 14 | FAIL | step proof |
| `Css.splitWs` | Css.lean:127 | 14 | FAIL | String/Format/Char |
| `FamilyMatch.matchStretch` | FamilyMatch.lean:118 | 14 | FAIL | structure param/result |
| `FilterApply.boxSizes` | FilterApply.lean:362 | 14 | FAIL | Array |
| `PngDecode.passLen` | PngDecode.lean:128 | 14 | FAIL | `/` `%` by var |
| `Text.trimChars` | Text.lean:341 | 14 | FAIL | Array |
| `Lighting.atanh2` | Filter/Lighting.lean:209 | 15 | FAIL | `/` `%` by var |
| `dashPattern` | Geom.lean:892 | 16 | FAIL | Array |
| `scaleDecimal` | Fixed.lean:55 | 16 | FAIL | Int/Fx |
| `F32.p2` | Canvas.lean:362 | 18 | FAIL | match shape |
| `Options.threads` | Render.lean:42 | 18 | FAIL | structure param/result |
| `Raster.hairPx` | Raster.lean:539 | 18 | FAIL | Array |
| `Render.Layer.back` | Render.lean:509 | 18 | FAIL | Option/tuple |
| `Svg.MaskUse.bbox` | Svg.lean:527 | 18 | FAIL | Option/tuple |
| `Svg.opacityToU8` | Svg.lean:1027 | 18 | FAIL | var×var `*` |
| `Turbulence.r64` | Filter/Turbulence.lean:139 | 18 | FAIL | Int/Fx |
| `Grad.clampTo` | Shader.lean:163 | 19 | FAIL | Int/Fx |
| `Turbulence.noise` | Filter/Turbulence.lean:226 | 19 | FAIL | Array |
| `Grad.Geom.conical` | Shader.lean:636 | 20 | FAIL | ctor/projection |
| `Brotli.runningSums` | Brotli.lean:350 | 21 | FAIL | Array |
| `Bidi.backScan` | Bidi.lean:477 | 22 | FAIL | structure param/result |
| `Xml.Event.text` | Xml.lean:44 | 23 | FAIL | ctor/projection |
| `sinCos16` | Geom.lean:38 | 23 | FAIL | Int/Fx |
| `Grad.RawDef.stops` | Shader.lean:374 | 25 | FAIL | Array |
| `Filter.Resolved.prims` | Filter.lean:249 | 26 | FAIL | Array |
| `Pat.roundDiv` | Pattern.lean:180 | 26 | FAIL | Int/Fx |
| `Grad.lerpUp` | Shader.lean:734 | 27 | FAIL | var×var `*` |
| `Svg.Paint.pattern` | Svg.lean:48 | 27 | FAIL | ctor/projection |
| `Raster.mkEdge` | Raster.lean:117 | 30 | FAIL | Int/Fx |
| `Font.unitsToFx16` | Font.lean:136 | 32 | FAIL | Int/Fx |
| `F32.bitLen` | Canvas.lean:386 | 35 | FAIL | do-block shape |
| `ShapeData.lookupRuns` | ShapeData.lean:30 | 50 | NOOUT | no verdict |
| `Svg.Shape.svgImage` | Svg.lean:321 | 50 | FAIL | structure param/result |
| `Svg.Doc.warnings` | Svg.lean:625 | 65 | FAIL | String/Format/Char |
| `Jpeg.idct` | Jpeg/Idct.lean:21 | 107 | FAIL | Array |
| `Bidi.levelCls` | Bidi.lean:85 | 191 | FAIL | structure param/result |
| `Bytes.toStr` | Bytes.lean:107 | ? | FAIL | ctor/projection |
| `FontSet.Entry.coverage` | FontSet.lean:83 | ? | FAIL | ctor/projection |
| `ImageData.Decoded.px` | ImageData.lean:22 | ? | FAIL | Array |
| `Jpeg.ycc` | Jpeg/Idct.lean:128 | ? | FAIL | do-block shape |
| `Synth.boldWidth` | Synth.lean:40 | ? | FAIL | Int/Fx |
| `VertOrient.isUpright` | VertOrient.lean:49 | ? | FAIL | step proof |

## 4. Soft-float `F32.*` (`abbrev F32 := Nat`, Canvas.lean:343)

All `LeanSvg.F32.*` functions probed. *Needs* = S(f) (every class in the closure). Soft-float is `Nat`-based, so the `Nat` var×var `*` row is the one §22 may cover.

| function | file:line | ≈lines | status | own first failure | needs (S(f)) |
|---|---|---|---|---|---|
| `F32.expo` | Canvas.lean:381 | 1 | OK | — | — |
| `F32.ge` | Canvas.lean:526 | 1 | FAIL | match shape | match shape; step proof |
| `F32.gt` | Canvas.lean:525 | 1 | FAIL | match shape | match shape; step proof |
| `F32.isNeg` | Canvas.lean:382 | 1 | FAIL | step proof | step proof |
| `F32.le` | Canvas.lean:524 | 1 | FAIL | match shape | match shape; step proof |
| `F32.mant` | Canvas.lean:380 | 1 | OK | — | — |
| `F32.neg` | Canvas.lean:466 | 2 | FAIL | step proof | step proof |
| `F32.ofNat` | Canvas.lean:450 | 2 | FAIL | `have`/`let` binding inside  | `have`/`let` binding inside ; do-block shape; match shape; step proof |
| `F32.sub` | Canvas.lean:492 | 2 | FAIL | `have`/`let` binding inside  | `have`/`let` binding inside ; do-block shape; match shape; step proof |
| `F32.mk` | Canvas.lean:383 | 3 | FAIL | step proof | step proof |
| `F32.fmin` | Canvas.lean:527 | 4 | FAIL | match shape | match shape; step proof |
| `F32.mul` | Canvas.lean:468 | 5 | FAIL | var×var `*` | do-block shape; match shape; step proof; var×var `*` |
| `F32.div` | Canvas.lean:494 | 7 | FAIL | step proof | do-block shape; match shape; step proof |
| `F32.lt` | Canvas.lean:514 | 10 | FAIL | match shape | match shape; step proof |
| `F32.fmax` | Canvas.lean:531 | 12 | FAIL | match shape | match shape; step proof |
| `F32.sqrt` | Canvas.lean:501 | 13 | FAIL | step proof | do-block shape; match shape; step proof |
| `F32.ofRat` | Canvas.lean:452 | 14 | FAIL | do-block shape | do-block shape; match shape; step proof |
| `F32.p2` | Canvas.lean:362 | 18 | FAIL | match shape | match shape |
| `F32.add` | Canvas.lean:473 | 19 | FAIL | step proof | do-block shape; match shape; step proof |
| `F32.toU8` | Canvas.lean:543 | 24 | FAIL | step proof | do-block shape; match shape; step proof; var×var `*` |
| `F32.norm` | Canvas.lean:421 | 29 | FAIL | do-block shape | do-block shape; match shape; step proof |
| `F32.bitLen` | Canvas.lean:386 | 35 | FAIL | do-block shape | do-block shape |

## 5. Inferences and caveats

- **Line counts** are inferred: next declaration's start line minus this one, within the same module (declaration ranges are not in the data). Nothing was read from the lean-svg source.
- **File names** are inferred from module names (`LeanSvg.Filter.Gamma` → `Filter/Gamma.lean`). Module and declaration line come from the committed `g.json` `L` field.
- **Only-X rows** use the first-failure class only. The probe stops at the first failure, so the body may contain further blockers. Treat these as lower bounds on what is needed.
- **NOOUT** (no verdict, probe killed or lost) is treated as unknown; closures touching one are excluded from *only X*.
- **§22 (⚠)**: NOTES §22 covers `*`, `/`, `%` on `Nat`/`UInt8/16/32/64` (`Testing/notes/frontx/NOTES.md:1373`). `Int`/`Fx` multiply or divide is not mentioned there, so rows whose blocker is `Int` arithmetic stay blocked (inference). Rows with a `/ %` by a non-2^k *constant* are not marked.
- **Classes** are the regex classes of `ana.py`; rare messages appear as `other:` and are not in the 12-class lists. Other classes present in the data but not requested: `/` `%` by non-2^k constant, ByteArray result, `Option` locals, loops over Array/List, mutable struct local, `have`/`let` in terms, resource limits, projection of non-constructors, tuple result, monadic (`Except`/`Shape.M`).
- **Leaves** are not the same as the 43 compiling functions: 10 of those call another user def, so they are not leaves.
