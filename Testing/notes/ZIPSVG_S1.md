# ZIPSVG_S1

Branch `zipsvg-s1`. Retries of the rows the two target notes mark as possibly unblocked by NOTES §22 (variable `*`, `/`, `%`).
Sources: `leanzip-targets:Testing/notes/LEANZIP_TARGETS.md` §1 rows 12–19 (lean-zip @7e10583);
`leansvg-targets:LEANSVG_TARGETS.md` §2 (lean-svg @df8e663, 22 rows). Repos cloned read-only at those revisions; code copied by line range, not retyped.

## 1. Zip: newly compiling functions (`Riscv/Frontx/ZipS1.lean`)

`wa_compile` with new entry names, verbatim `countLengthsFast`, `kraftSumFast`, `nextCodesFast` (+ `go` helpers). All three compile.

| entry | copied from | command | test |
|---|---|---|---|
| `s1countlengths` | `Zip/Native/Inflate.lean:536@7e10583` | `wa_compile` | `wa_s1countlengths`: 50 cases ok (QEMU == Sail == Lean) |
| `s1kraft` | `Zip/Native/Inflate.lean:555@7e10583` | `wa_compile` | `wa_s1kraft`: 50 cases ok |
| `s1nextcodes` | `Zip/Native/Inflate.lean:587@7e10583` | `wa_compile` | `wa_s1nextcodes`: 50 cases ok |

Caveat: these three definitions already compile on `wa` in `Riscv/Frontx/WaMul.lean` (`kraftE`, `nextCodesE`) and `WaLeanZip.lean` (`countLengthsE`), so this is a re-check under new names, not a new capability. Not retried: the `frontx_compile` (list) path for these rows, and the other zip rows (`fillSlots`, `countLongCodes`, etc.), which are still blocked on other features per the target note.

Test command: `python3 Testing/asm/frontx_test.py check 50 <name>`. Emit: `lake env lean --tstack=400000 Testing/asm/emit_s1.lean`. Build for emit: `lake build Riscv.Frontx.ZipS1`.

## 2. SVG: 0 of 22 compile (`Riscv/Frontx/SvgS1.lean`)

Each function is copied verbatim from lean-svg @df8e663 with its namespace, the constants it needs copied verbatim above it (`Svg.opacityOne`, `Canvas.opGrid`, `Grad.opacityOne`, `Grad.recipShift`, `Grad.opacityCube`, `Lighting.S`, `Bytes.at'`, `Jpeg.byteAt`), and a plain `frontx_compile <name>` with no `requires` clause. No test cases were generated for SVG (nothing compiled).

| # | function | source (df8e663) | Lean namespace | first error (exact) | goal (first line) |
|---|---|---|---|---|---|
| 1 | `cov16` | Clip.lean:106 | `LeanSvg.Clip` | No goals to be solved | |
| 2 | `recipOf` | Shader.lean:731 | `LeanSvg.Grad` | frontx: could not prove | `Proven.BExp.denote` |
| 3 | `premulU8` | Image.lean:236 | `LeanSvg.Image` | frontx: could not prove | `Proven.BExp.denote` |
| 4 | `to8` | PngDecode.lean:226 | `LeanSvg.PngDecode` | frontx: could not prove | `Proven.BExp.denote` |
| 5 | `peekBits` | Jpeg/Huffman.lean:26 | `LeanSvg.Jpeg` | frontx: could not prove | `Proven.BExp.denote` |
| 6 | `stopAlpha8` | Shader.lean:896 | `LeanSvg.Grad` | No goals to be solved | |
| 7 | `opacityQ` | PatternRender.lean:204 | `LeanSvg.Pat` | frontx: could not prove | `Proven.BExp.denote` |
| 8 | `mulOpacity` | Svg.lean:1025 | `LeanSvg.Svg` | frontx: could not prove | `Proven.BExp.denote` |
| 9 | `premul` | Canvas.lean:47 | `LeanSvg.Canvas` | frontx: could not prove | `Proven.BExp.denote` |
| 10 | `unpremul` | Canvas.lean:55 | `LeanSvg.Canvas` | frontx: could not prove | `Proven.BExp.denote` |
| 11 | `peek` | Inflate.lean:27 | `LeanSvg.Inflate` | frontx: could not prove | `Proven.BExp.denote` |
| 12 | `mulQ` | Filter/Lighting.lean:294 | `LeanSvg.Lighting` | frontx: could not prove | `Proven.BExp.denote` |
| 13 | `zlibLen` | Png.lean:166 | `LeanSvg.Png` | frontx: could not prove | `Proven.BExp.denote` |
| 14 | `sample` | PngDecode.lean:216 | `LeanSvg.PngDecode` | frontx: could not prove | `(Proven.BExp.denote` |
| 15 | `iirCoeffs` | FilterApply.lean:387 | `LeanSvg.FilterApply` | Unknown constant `Nat.sqrt` (line 176, inside iirCoeffs, before its frontx_compile); then frontx: could not prove | `Proven.BExp.denote` |
| 16 | `lerpDown` | Shader.lean:763 | `LeanSvg.Grad` | frontx: could not prove | `Proven.BExp.denote` |
| 17 | `opacityQ` | Render.lean:471 | `LeanSvg.Render` | frontx: could not prove | `Proven.BExp.denote` |
| 18 | `passLen` | PngDecode.lean:129 | `LeanSvg.PngDecode` | frontx: could not prove | `Proven.BExp.denote` |
| 19 | `atanh2` | Filter/Lighting.lean:211 | `LeanSvg.Lighting` | frontx: could not prove | `Proven.BExp.denote` |
| 20 | `opacityToU8` | Svg.lean:1040 | `LeanSvg.Svg` | frontx: could not prove | `Proven.BExp.denote` |
| 21 | `lerpUp` | Shader.lean:752 | `LeanSvg.Grad` | frontx: could not prove | `Proven.BExp.denote` |
| 22 | `expS` | Filter/Lighting.lean:226 | `LeanSvg.Lighting` | frontx: could not prove | `Proven.BExp.denote` |

Notes on the table:
- `frontx: could not prove` with a `Proven.BExp.denote` goal is the front end's side-condition obligation; no `requires` was supplied. I did not add `requires` bounds (that would change the retry), so the goals are unresolved. Which operand bound each needs is not verified here.
- `No goals to be solved` (cov16, stopAlpha8) is an extra Lean error reported after the same failed proof.
- `opacityQ` appears twice (`LeanSvg.Pat` at `PatternRender.lean:204`, `LeanSvg.Render` at `Render.lean:471`).
- `iirCoeffs` uses `Nat.sqrt`, which is not in Lean 4.29 core (the depth note says it is in 4.34); that error comes first.

## 3. Not found

- No `LEANZIP_TARGETS` or `LEANSVG_TARGETS` row is marked for higher-order arguments (§27). Neither target file mentions §27 or HOF. So no `frontx_hof` retry was made.
- `LEANZIP_TARGETS.md` lives at `Testing/notes/LEANZIP_TARGETS.md` on `leanzip-targets`, not at the repo root.

## 4. Setup

- Built `lake build Frontx` (303 jobs, success) on Lean 4.29.0 with the sail deps from `build-cache`.
- Installed `zstd`, `elan`, and (for the harness) `gcc-riscv64-linux-gnu`, `qemu-system-misc`.
- No `sorry`, no axioms, no `native_decide`. Compiler sources not modified.
