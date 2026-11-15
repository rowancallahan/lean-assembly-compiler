# lean-svg compiled verbatim: first leaves through the front end

Branch `leansvg-verbatim`. lean-svg = `rowancallahan/lean-svg` @ `df8e663` (Lean v4.34; here v4.29.0).
Files: `Testing/leansvg/Orig.lean` (the definitions, the `frontx_compile` / `frontx_implements` calls, the case
emitter), `Testing/leansvg/cases/*.cases`, `Testing/leansvg/words/*.words`. Run: `lake env lean --tstack=4000000
Testing/leansvg/Orig.lean` (≈30 s; the 18 `error` lines it prints ARE the rejections below, kept on purpose).
`Spec/` and `Compiler/` are untouched; `Riscv/Frontx` is unchanged.

Not done: the QEMU / Sail-C-emulator runs (`frontx_test.py`): there is no QEMU or RISC-V gcc in this container. The
`.words` of the five accepted entry points are emitted and their `.cases` are asserted equal to `Res.enc (entry xs)`
inside Lean, but the words were not executed on a machine.

## 1. lean-svg bottom-up (non-font files: 1 490 defs; heuristic, name-based call graph, nothing type-checked)

Toolchain facts as in `frontx/NOTES.md` §3 (0 `partial`, 24 fuel recursions, no `Float`, `Int` = `Fx` fixed point).

| level (callee depth) | defs | what | types / recursion | size |
|---|---|---|---|---|
| 0: no project callees | 441 (29 %) | limits and tags (~280 constants); byte classifiers (`Bytes.isWs`…, `at'`); digit values (`Svg.hexVal`, `Image.b64Val`, `Font.b64Digit`); fixed-point scalars (`Fx.clamp/floor/round/abs`, `Raster.toFDot6/divRound`, `Font.roundDiv14`, `Geom.degToRad16`); colour channels (`Canvas.div255/premul/unpremul/pack`, `Image.premulU8`); `PngDecode.paeth/to8`; `ShapeText.utf8Len`; the only number→text function `Use.fmtFixed` (core `toString`, no digit loop in the repo) | `Nat` (channels, bytes), `Int` (everything geometric), `UInt8`; no recursion | 1–7 lines, median 1 |
| 1–3 | 265 | byte scans (`skipWhile`, `findByte`, `startsWith`, `eqAscii`), `be32/le16/u16`, `Fixed.parseDecimal`, `Pt`/`Mat` ops, `sinCos16`, CRC/Adler, base64/percent decode | + `ByteArray`, `Option`, tuples, one `for`; 3 fuel recursions | 3–60 |
| 4–30 | ≈480 | path commands, curve flattening, dashes, rasteriser, CSS, gradients, filter primitives, bit readers (Inflate, Brotli, JPEG) | `Array`, structures, closures, nested `for`, fuel recursion | 10–250 |
| 31–84 | ≈300 | `Svg` element tree (`Svg.lean`, 5 050 lines), `Text.layout` (depth 84), `Render.render` (`Render.lean:1099`, depth 62) | `Array (structure)`, `String`, `HashMap`, `StateM` | 20–1 000 |

Per-def feature counts (regex, the whole set): structure/`List` 528, `Array`/`push` 512, `Int` 413, closures 343, variable×variable `*` 245,
`String`/`Char` 170, several loops 145, `>>>` 92, `/` `%` by a variable 85, by a non-power-of-two constant 35, `HashMap`/`StateM`/`Float` 11.

## 2. The leaves (22 definitions, all verbatim; `Bytes.at'`, `isWs`, `isDigit` are controls known to compile)

Copied by `sed`-style slicing of the source lines (so byte-identical), provenance in the header comment of each block.
**Edits: none to any definition.** Context only: each block is wrapped in its original `namespace`; `hexVal` gets
`open LeanSvg.Bytes` (Svg.lean opens `Bytes`; without it `isDigit` is unknown); the support definitions `Fx`, `Fx.one`,
`Fx.maxVal` are copied from `Fixed.lean:17,21,25` (needed by `Fx.clamp`; `one` unused). No Lean-version API edit was
needed for these 22 (the 4.34 → 4.29 differences, e.g. `String.ofList`, did not occur in these bodies; `fmtFixed`
type-checks as is).

| result of `frontx_compile` (unmodified) | function (file:line@df8e663) |
|---|---|
| **accepted**, `f.exec` with `propext, Classical.choice, Quot.sound` | `Bytes.at'` (Bytes:15), `Bytes.isWs` (:18), `Bytes.isDigit` (:19), `Image.b64Val` (Image:93, 11 obligations), `Svg.hexVal` (Svg:690, 2 result components, 15 obligations), `ShapeText.utf8Len` (ShapeText:63, 7 obligations) |
| accepted but the command logs 3 × `error: No goals to be solved`; `exec` exists, no `sorry`, standard axioms | `Canvas.pack` (Canvas:68) |
| rejected | the other 15 below |

Exact messages (first line; `(…)` = the term printed on the next line):

| function (file:line) | rejection | blocking feature |
|---|---|---|
| `Canvas.div255` (Canvas:38) `(x + 255) >>> 8` | `frontx: could not prove` `denote … lshr (add (var 4) 255#64) 8#64 = rN ((x + 255) >>> 8)`; ``simp` made no progress`` | `Nat` `>>>` (no `rN` lemma; only `+ - &&& ||| <<<`) |
| `Canvas.premul` (Canvas:47) `(c*a + 127)/255` | `frontx: unsupported term` `instHMul.1 c a` | variable × variable `*` (also `/ 255`) |
| `Canvas.unpremul` (Canvas:55) | `frontx: unsupported term` `instHDiv.1 (c * 510 + a) (2 * a)` | `/` by a variable (also `Nat.min`, not reached) |
| `Image.premulU8` (Image:236) | `frontx: unsupported term` `instHMul.1 c a` | var × var `*` (then `>>>`) |
| `Fx.clamp` (Fixed:27) | `frontx: unsupported result type` `LeanSvg.Fx` | `Int` (`Fx := Int`) |
| `Fx.floor` (Fixed:38) `Int.ediv a 256` | `unsupported result type` `Int` | `Int` (`ediv` by 2^k) |
| `Fx.round` (Fixed:40) | `unsupported result type` `Int` | `Int` |
| `Fx.abs` (Fixed:41) | `unsupported result type` `LeanSvg.Fx` | `Int` |
| `Raster.toFDot6` (Raster:531) `Int.tdiv a 4` | `unsupported result type` `Int` | `Int` (`tdiv` by 2^k) |
| `Raster.divRound` (Raster:534) | `unsupported result type` `Int` | `Int`, `ediv` by `2*d` (variable) |
| `Font.roundDiv14` (Font:134) | `unsupported result type` `Int` | `Int` (`ediv` by 2^14) |
| `degToRad16` (Geom:34) | `unsupported result type` `Int` | `Int`, `emod`/`ediv` by constants 92160 / 46080 (not 2^k) |
| `PngDecode.paeth` (PngDecode:142) | `frontx: could not prove` `denote (… set 9 (rN (a+b))).set 10 (rN (2*c)) … = rN (if a + b ≥ 2 * c then a + b - 2 * c else 2 * c - (a + b))`; `frontx_u8_facts: no byte` | truncated `Nat` subtraction guarded by a compound test (translator emits the `ult … ite 0 sub` form, the step proof does not close) |
| `PngDecode.to8` (PngDecode:226) | `frontx: could not prove` `denote (and (lshr (var 5) 8) 255) = r8 (v >>> 8).toUInt8`; ``simp` made no progress`` | `Nat` `>>>` then `.toUInt8` (also `255 / ((1 <<< d) - 1)`: `/` by variable, `*` var × var, `<<<` by variable) |
| `Use.fmtFixed` (Use:151) | `frontx: unsupported result type` `String` | `String` result (`toString`, `++`, `List.replicate`, `5 ^ bits`, `Int.natAbs`) |

Only the first blocker is reported by the front end; the features listed after the first are read off the source,
not tested.

Machine theorems (`frontx_entry` + `frontx_implements`, `g.implements1`, the standard model axioms): the front
end needs `g xs := f xs …` with the byte array first, so the leaves are called through new wrappers (new code, the
leaf is not touched): `At.f xs i` (compiled, `requires i + 8 < 2^64`) and `Entry.f xs := At.f xs 0`.
Got: `Entry.b64Val` (117 lines of words file: 6 slots), `Entry.isWs` (3), `Entry.isDigit` (3), `Entry.at3 xs := at' xs 3` (2),
`Entry.pack` (12 slots; 4 bytes in, `Nat` out). Not obtained: `hexVal` (`match Svg.hexVal c with …` in the wrapper:
`frontx: unsupported Bool`, a `match` on the `Option` result of a call), `utf8Len` (3-byte argument: `(deterministic)
timeout at whnf` at 2 000 000 heartbeats). Those two leaves are accepted by `frontx_compile`, only the machine entry is missing.

## 3. Cases (executed Lean)

`Testing/leansvg/cases/<f>.cases`, `input-hex result-hex` per line (frontx-words format; `-` = empty), 2 131 lines
for 22 functions (256 inputs for the byte classifiers, 52–60 for the others). Written by `#eval` of the unmodified
definitions (interpreter) in `Orig.lean`. Encodings: `Nat` argument 16-bit LE (a colour channel, `b64Val`'s byte, `isWs`'s byte: 1 byte; `utf8Len`: 3 bytes;
`pack`: r g b a bytes), `Int` 32-bit two's complement LE, `to8`: depth byte ++ 16-bit value, `at'`: 16-bit index ++ the array
(`at3`: the array only). Result: `Nat` 8 bytes LE, `Int` 8 bytes two's complement LE, `UInt8` / `Bool` 1 byte,
`hexVal` as `Nat` with `none ↦ 255` (so 8 bytes), `fmtFixed` the UTF-8 bytes. For `b64Val`, `isWs`, `isDigit`, `at3`, `pack` the
cases are asserted against `Res.enc (Entry.f xs)` while writing (so the same file would be the QEMU/Sail test input).
The 15 rejected functions have cases but no `.words`.

## 4. Features by what they unlock

Over the 15 rejected leaves above (cumulative; later rows count only functions all of whose features are covered; the
feature sets beyond the first blocker are read from the source):

| # | feature to add | newly unlocked | cumulative of 15 |
|---|---|---|---|
| 1 | `Int` scalars: type, `+ - neg`, compare, `ediv`/`tdiv` by 2^k | `Fx.clamp`, `Fx.floor`, `Fx.round`, `Fx.abs`, `toFDot6`, `roundDiv14` | 6 |
| 2 | `Nat` `>>>` (an `rN` lemma, `Nat.shiftRight` by a literal) | `div255` | 7 |
| 3 | `/` `%` by a non-power-of-two constant (`Int` too) | `degToRad16` | 8 |
| 4 | general variable × variable `*` | `premul`, `premulU8` | 10 |
| 5 | `/` by a variable (`Nat`, `Int`), shift by a variable | `divRound`, `to8` | 12 |
| 6 | truncated `Nat` subtraction under a compound guard | `paeth` | 13 |
| 7 | `Nat.min` (and the like) | `unpremul` | 14 |
| 8 | `String` results, `toString`, `^`, `List.replicate` | `fmtFixed` | 15 |

Over all 1 490 non-font defs (greedy by marginal unlock, regex feature sets and the name-based call graph, so
rough; a def counts as unlocked when all its own features and all its callees are covered; 257 defs need none of
these features): `Int` +77 (334), `Array`/alloc/`push` +40 (374), structure/`List` values +38 (412), closures +47 (459),
var×var `*` +56 (515), `Nat >>>` +58 (573), `String`/`Char` +58 (631), `/` `%` by a variable +345 (976),
several loops +131 (1 107), `/` `%` by non-2^k constants +340 (1 447), `HashMap`/`StateM`/`Float` +43 (1 490).
The two +340 jumps are transitive (a division deep in a shared leaf); read them as "gate for most of the middle and top
levels", not as a count of functions that need only that feature. Order of work that this suggests: `Int` first
(every geometric leaf), then the arithmetic operators (`>>>`, `*`, `/`, `%`), then arrays with `push`; `String` last.
