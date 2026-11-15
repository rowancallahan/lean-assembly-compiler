# lean-svg verbatim through the front end

lean-svg (`github.com/rowancallahan/lean-svg` @ df8e663, Lean 4.34.0) is a long-term compile target AS IS. Branch `leansvg-verbatim`.
Files: `Testing/leansvg/Orig.lean` (22 leaf functions verbatim + `Gen` case emitter), `analyze.py` (bottom-up listing, `defs.json`),
`rank.py` (feature ranking), `run.sh` + `report.py` (front-end attempts), `cases/*.cases` (executed Lean).
Reproduce: `Testing/leansvg/run.sh > /tmp/orig.out; python3 report.py /tmp/orig.out` (8 s; needs `lake build Frontx`).

## 1. Pure functions bottom-up

`python3 Testing/leansvg/analyze.py /path/to/lean-svg`: 101 files in the import closure of `LeanSvg/Render.lean`, 1665 `def`/`abbrev`; heuristic call graph by
identifier match (not type-checked, so name clashes add edges): level 0 = calls no other project def. Levels: 0: 546, 1: 240, 2: 102, 3: 58, 4: 63, 5: 46, 6: 43, 7: 28, 8: 8, 9: 13, 10: 6, 11: 11, 12+: 501
(12+ includes false cycles from name clashes). 483 level-0 defs are outside the generated data files (`Fonts`, `*Data`, `*Table`, `Stix*`).
Leaf families: byte predicates (`Bytes`), channel/pixel arithmetic (`Canvas`, `FilterApply`, `Clip`), fixed-point `Int` helpers (`Fixed`, `Geom`, `Shader`),
PNG/Jpeg helpers (`PngDecode`, `Jpeg.*`), Unicode class tests (`Text`, `Shape`), record accessors (`Shape.GInfo.*`).

## 2. Front end on 22 leaves, unmodified (`frontx_compile f`, no `with`/`requires`)

Edits to the sources: namespaces only (`LeanSvg.X` -> `LeanSvgOrig.X`), `open Bytes (at')` where the file has it, `abbrev Fx := Int` copied; none for the Lean version.
10 accepted (F1-F6, F13, F14, F17, F18), 1 accepted with spurious errors (F10), 11 rejected.

| F | function (file:line) | result | blocking feature / exact message |
|---|---|---|---|
| F1 | `Bytes.at'` (Bytes:15) | ACCEPTED | — |
| F2 | `Bytes.isDigit` (Bytes:19) | ACCEPTED | — |
| F3 | `Bytes.toLower` (Bytes:23) | ACCEPTED | — |
| F4 | `Font.b64Digit` (Font:554) | ACCEPTED | — |
| F5 | `Image.hexDigit` (Image:66) | ACCEPTED | — |
| F6 | `Image.chans` (Image:421) | ACCEPTED | — |
| F7 | `Image.round32` (Image:426) | REJECTED | `Int` parameter |
| F8 | `Canvas.div255` (Canvas:38) | REJECTED | unbounded `Nat`: `x + 255` can wrap; needs `x + 255 < 2^64` |
| F9 | `Canvas.premul` (Canvas:47) | REJECTED | `c * a + 127` needs a bound (`c * a + 127 < 510` demanded by the one-subtraction division); var×var `*` |
| F10 | `Canvas.pack` (Canvas:68) | ACCEPTED* | — (but 3 spurious `No goals to be solved` errors: front-end defect on large constant `*`) |
| F11 | `Canvas.div65025` (Canvas:147) | REJECTED | unbounded `Nat`: `x * 67636241` wraps; needs a bound on `x` |
| F12 | `PngDecode.be32` (PngDecode:36) | REJECTED | unbounded `Nat` index: `i + 1 < 2^64` (the notes' `with fun _ i => i + 3 < 2^64`) |
| F13 | `PngDecode.channels` (PngDecode:51) | ACCEPTED | — |
| F14 | `PngDecode.validDepth` (PngDecode:54) | ACCEPTED | — |
| F15 | `PngDecode.passLen` (PngDecode:129) | REJECTED | `/` by a variable (`n - o + d - 1) / d`) |
| F16 | `PngDecode.paeth` (PngDecode:142) | REJECTED | unbounded `Nat`: `a + b`, `2 * c` wrap; bounds needed on the three arguments |
| F17 | `ShapeText.utf8Len` (ShapeText:63) | ACCEPTED | — |
| F18 | `Text.isHan` (Text:119) | ACCEPTED | — |
| F19 | `Grad.clampTo` (Shader:163) | REJECTED | `Int` parameter and result |
| F20 | `Fx.abs` (Fixed:41) | REJECTED | `Fx := Int` parameter and result |
| F21 | `Fx.min` (Fixed:42) | REJECTED | `Fx := Int` parameter and result |
| F22 | `Png.adlerChunk` (Png:113) | REJECTED | unbounded `Nat` index: `i + 1 < 2^64` (fuel recursion) |

`*` F10 `Canvas.pack`: `Canvas.pack.exec` is produced and depends on the 3 standard axioms only, but the command reports three errors `No goals to be solved`.
F7, F19-F21 additionally print `PANIC at Lean.Expr.appArg! … application expected` after the `unsupported parameter/result type` error (error path of `frontx_compile`).
Exact messages: `python3 report.py` output / `/tmp/orig.out`; the first lines are in the table above.

## 3. Cases

`Testing/leansvg/cases/<function>.cases` (22 files): one line per input, `<args> => <result>`, from `#eval` of the verbatim function (ByteArray hex, `-` = empty;
inputs: all 256 bytes for `UInt8` functions, edge values 0, 1, 255, 256, 2^32±1, 2^63, 2^64±1, 2^70 and 50 pseudo-random for `Nat`/`Int`, both signs for `Int`).
Not yet run on QEMU: only F1-F6, F13, F14, F17, F18 compile, and none has an entry point (`frontx_entry`) here; the cases are the oracle for when they do.

## 4. Features ranked by functions unlocked

Heuristic (`rank.py`, regexes over comment-stripped source, not type-checked): a def is unlocked when its own blocking features and those of everything it calls (transitively) are provided.
Features already provided are those observed accepted above and in NOTES 9-19 (scalar `Nat`/`UIntN`/`Bool`, `if`/`match`, `ByteArray` reads, `Option`/tuple results, range loops, fuel recursion, `*` `/` `%` by constants).
"structure / inductive values" is an upper bound: structures of scalar fields exist (NOTES 14); the regex counts any project type in a signature.


#### lean-svg without generated data files: 1464 defs

already unlocked with no new feature: 190

| step | feature added | newly unlocked | cumulative | % of defs |
|---|---|---|---|---|
| 1 | structure / inductive values | +52 | 242 | 16% |
| 2 | Int / Fx (signed) | +66 | 308 | 21% |
| 3 | Array (not ByteArray) | +55 | 363 | 24% |
| 4 | unbounded Nat contract (index/overflow bound) | +51 | 414 | 28% |
| 5 | variable * / % operand | +120 | 534 | 36% |
| 6 | closures / higher-order | +75 | 609 | 41% |
| 7 | exponentiation / sqrt | +181 | 790 | 53% |
| 8 | String / Char | +161 | 951 | 64% |
| 9 | ByteArray output (push/set/append) | +269 | 1220 | 83% |
| 10 | StateM monad | +215 | 1435 | 98% |
| 11 | HashMap | +29 | 1464 | 100% |

single-feature blocking (defs whose only missing feature is it):
structure / inductive values: 52; Int / Fx (signed): 51; Array (not ByteArray): 35; unbounded Nat contract (index/overflow bound): 23; String / Char: 18; closures / higher-order: 12; exponentiation / sqrt: 8; ByteArray output (push/set/append): 5; StateM monad: 1

feature frequency (defs needing it, incl. via callees):
unbounded Nat contract (index/overflow bound): 905; Array (not ByteArray): 867; structure / inductive values: 856; variable * / % operand: 817; Int / Fx (signed): 806; closures / higher-order: 783; String / Char: 583; exponentiation / sqrt: 554; ByteArray output (push/set/append): 436; StateM monad: 238; HashMap: 29

#### leaves only (level 0, no data files): 483 defs

already unlocked with no new feature: 169

| step | feature added | newly unlocked | cumulative | % of defs |
|---|---|---|---|---|
| 1 | structure / inductive values | +40 | 209 | 43% |
| 2 | Int / Fx (signed) | +46 | 255 | 52% |
| 3 | Array (not ByteArray) | +47 | 302 | 62% |
| 4 | unbounded Nat contract (index/overflow bound) | +33 | 335 | 69% |
| 5 | variable * / % operand | +51 | 386 | 79% |
| 6 | closures / higher-order | +27 | 413 | 85% |
| 7 | String / Char | +28 | 441 | 91% |
| 8 | exponentiation / sqrt | +23 | 464 | 96% |
| 9 | StateM monad | +9 | 473 | 97% |
| 10 | ByteArray output (push/set/append) | +8 | 481 | 99% |
| 11 | HashMap | +2 | 483 | 100% |

single-feature blocking (defs whose only missing feature is it):
structure / inductive values: 40; Int / Fx (signed): 40; Array (not ByteArray): 33; unbounded Nat contract (index/overflow bound): 14; String / Char: 13; closures / higher-order: 10; exponentiation / sqrt: 8; ByteArray output (push/set/append): 2; StateM monad: 1

feature frequency (defs needing it, incl. via callees):
Int / Fx (signed): 104; Array (not ByteArray): 104; structure / inductive values: 101; unbounded Nat contract (index/overflow bound): 77; variable * / % operand: 63; closures / higher-order: 48; String / Char: 32; exponentiation / sqrt: 23; StateM monad: 9; ByteArray output (push/set/append): 8; HashMap: 2

Reading: a quick first tier is the arithmetic contracts (`Int`, bounds on `Nat`, `/` by a variable), which account for all 11 rejections above (`Int`: 4, `Nat` bounds: 5, `*`/`/` var: 2);
beyond them every further 10% needs a data-structure feature (`Array`, `String`, closures, `ByteArray` output, `StateM`).
