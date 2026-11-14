# Survey of lean-svg for a verified compiler front end

Repo: `scratchpad/svg/lean-svg` (read-only, not built). Toolchain file: `leanprover/lean4:v4.34.0`. `lakefile.toml` declares no dependencies ("Lean core only"); the only non-project import is `Std.Data.HashMap`.
All paths below are relative to the repo root. Scripts used: `survey/closure.py`, `survey/feat.py`, `survey/f2.py`, `survey/st.py`; raw output in `survey/feat.txt`, `survey/closure.txt`.

Method caveats (apply to all numbers):
- "render's call graph" is approximated by **all `.lean` files transitively imported by `LeanSvg/Render.lean`** (101 files). This over-approximates: defs in those files not reachable from `render` are counted.
- Feature counts are regex heuristics on comment-stripped, string-literal-emptied source, per top-level declaration body (a declaration = from a column-0 `def/abbrev/instance` line to the next top-level command). Nothing was type-checked.

---

## A. Small byte-level pieces

"BStmt lacks" refers to: 24 64-bit vars, byte load/store on fixed blocks, `while`; no calls, stack, heap alloc, 8-byte loads, mul/div/mod.
Common to nearly every item: (i) `Nat` typed indices/results (unbounded in Lean; here bounded by `bs.size`, so need a boundedness side-condition), (ii) calls to helper defs (BStmt has no calls → must inline), (iii) bounds-checked read `Bytes.at'` (returns 0 past end) or `bs[i]'h` (proof-carrying index).

| # | Function | file:line | lines | Signature | Types | Recursion | Mutates Array/ByteArray | Lookup table | `*` `/` `%` | Calls | BStmt lacks |
|---|---|---|---|---|---|---|---|---|---|---|---|
| 1 | `Png.crcTable` | LeanSvg/Png.lean:28 | 5 | `def crcTable : Array UInt32` | UInt32, Array, List (`List.range 8`), Fin (`i.val`) | none; `Array.ofFn` + `List.foldl` with closure | builds a 256-entry Array | is the table | none (`&&& ^^^ >>>`) | `Array.ofFn`, `List.range`, `List.foldl`, `Nat.toUInt32` | higher-order `ofFn`/`foldl`; produces a table of 4-byte entries (BStmt stores bytes only → 4 stores per entry); 32-bit truncation |
| 2 | `Png.crcAdvance` (+ `crcTable1..3`, :39-41) | Png.lean:36 | 2 | `def crcAdvance (t : Array UInt32) : Array UInt32` | UInt32, Array | none; `Array.map` closure | new Array | reads `crcTable` | none | `Array.map`, `Array.getD`, `UInt32.toNat` | map over Array of UInt32; 4-byte loads/stores |
| 3 | `Png.crcBytes` | Png.lean:52 | 3 | `def crcBytes (bs : ByteArray) (start stop : Nat) (c : UInt32) : UInt32` | UInt32, UInt8, Nat, ByteArray, Array UInt32 | none; `ByteArray.foldl` with closure over sub-range | no | yes: `crcTable` (256 × UInt32) | none | `ByteArray.foldl`, `Array.getD`, `UInt8.toUInt32`, `UInt32.toNat` | closure/fold; 32-bit table load (only byte loads → 4 loads + shifts/ors); `foldl` clamps `stop` to `bs.size` |
| 4 | `Png.crcRun4` | Png.lean:66 | 19 | `def crcRun4 (bs : ByteArray) (i fuel : Nat) (c : UInt32) : UInt32` | UInt32, Nat, ByteArray | structural on `fuel` (`match fuel with \| 0 \| fuel'+1`), tail-recursive; non-tail fallback call to `crcBytes` | no | yes: 4 tables `crcTable..crcTable3` | `4 * (fuel'+1)` in fallback branch; index `i+4` | `crcBytes`, `Array.getD`, `toUInt32`, `toNat`; proof terms `by omega` (3) for `bs[i]'…` | 4 table blocks with 32-bit entries; call to `crcBytes` (inline); dependent `if h :` and index proofs; mul by 4 (expressible as shl) |
| 5 | `Png.crc32Range` | Png.lean:88 | 6 | `def crc32Range (bs : ByteArray) (start stop : Nat) : Nat` | Nat, UInt32, ByteArray | none | no | via callees | `/ 4`, `* 4` | `Nat.min`, `crcRun4`, `crcBytes`, `UInt32.toNat` | calls; `/4`,`*4` (shift-expressible); `Nat.min` |
| 6 | `Png.crc32` | Png.lean:95 | 1 | `def crc32 (bs : ByteArray) : Nat` | Nat, ByteArray | none | no | via callees | none | `crc32Range`, `ByteArray.size` | call |
| 7 | `Png.adlerChunk` | Png.lean:113 | 6 | `def adlerChunk (rgba : ByteArray) (i fuel : Nat) (a b : UInt64) : UInt64 × UInt64` | UInt64, Nat, ByteArray, Prod | structural on `fuel`, tail-recursive | no | no | none (adds only) | `ByteArray.size`, `rgba[i]` under `if _ : i < rgba.size`, `UInt8.toUInt64` | pair result (two output vars); dependent `if`; otherwise within BStmt (add, byte load, loop) |
| 8 | `Png.adlerChunk4` | Png.lean:122 | 14 | `def adlerChunk4 (rgba : ByteArray) (i fuel : Nat) (a b : UInt64) : UInt64 × UInt64` | UInt64, Nat, ByteArray, Prod | structural on `fuel`, tail-recursive; fallback tail call to `adlerChunk` | no | no | `4 * (fuel'+1)` in fallback | `adlerChunk`, `toUInt64`; `by omega` (3) | pair result; call to `adlerChunk` (inline as second loop); mul by 4 (shl) |
| 9 | `Png.adler32Rows` | Png.lean:137 | 16 | `def adler32Rows (rgba : ByteArray) (rowBytes h : Nat) : Nat := Id.run do` | Nat (accumulators `a b`), UInt64 (via callees), ByteArray | `Id.run do`, 2 nested `for … in [0:n]`, `let mut a b` | no | no | `% 65521` ×3, `/ 5552`, `/ 4`, `y * rowBytes`, `c * 5552`, `quads * 4` | `adlerChunk4`, `adlerChunk`, `Nat.min`, `Nat.toUInt64`, `UInt64.toNat` | **`% 65521`, `/ 5552`, general `*`** (no mul/div/mod op); calls; tuple projections `.1 .2` |
| 10 | `Png.be32` (u32 big-endian writer) | Png.lean:154 | 3 | `def be32 (n : Nat) : ByteArray` | Nat, UInt8, ByteArray | none | allocates ByteArray, 4 × `push` | no | none (`>>> &&&`) | `ByteArray.empty`, `ByteArray.push`, `Nat.toUInt8` | **heap allocation / growable output** (returns fresh ByteArray); as "write 4 bytes at offset" into a fixed block it is expressible |
| 11 | `Png.chunk` | Png.lean:158 | 3 | `def chunk (typ : String) (data : ByteArray) : ByteArray` | String, ByteArray, Nat | none | allocates; `++` ×4 | via `crc32` | none | `String.toUTF8`, `ByteArray.append`, `be32`, `crc32` | String; allocation/append; calls |
| 12 | `Png.blockHeader` | Png.lean:173 | 6 | `@[inline] def blockHeader (out : ByteArray) (pos rawSize : Nat) : ByteArray` | Nat, UInt8, ByteArray | none | 5 × `push` on `out` | no | none | `Nat.min`, `push`, `toUInt8` | output buffer append (needs out-length variable + store into block) |
| 13 | `Png.storedPieces` / `Png.storedRows` | Png.lean:184 / :197 | 10 / 8 | `def storedPieces (rgba : ByteArray) (rawSize stop : Nat) : Nat → ByteArray → Nat → Nat → ByteArray × Nat`; `def storedRows (rgba : ByteArray) (rowBytes rawSize pieces : Nat) : Nat → Nat → ByteArray → Nat → ByteArray` | Nat, ByteArray, Prod | equation-style structural recursion on fuel, tail-recursive; `storedRows` calls `storedPieces` (nested loop) | `out.push`, `ByteArray.copySlice` into `out` | no | `% 65535` ×3, `y * rowBytes` | `blockHeader`, `ByteArray.copySlice`, `Nat.min` | `% 65535`, general `*`; block copy (`copySlice` = inner byte loop); threaded mutable output buffer |
| 14 | `Png.zlibLen` | Png.lean:166 | 4 | `def zlibLen (rowBytes h : Nat) : Nat` | Nat | none | no | no | `h * (rowBytes+1)`, `/ 65535`, `nblocks * 5` | none | general `*`, `/ 65535` |
| 15 | `Png.encode` | Png.lean:224 | 14 | `def encode (w h : Nat) (rgba : ByteArray) : ByteArray := Id.run do` | Nat, ByteArray, String | `Id.run do`, `let mut out`, no loop | `emptyWithCapacity` + 7 × `++` | via callees | `w * 4`, `w*h` sizes | `zlibLen`, `chunk`, `be32`, `zlibStoredRows`, `crc32Range`, `String.toUTF8` | allocation of output sized by input; calls |
| 16 | `Image.b64Val` | LeanSvg/Image.lean:93 | 7 | `@[inline] def b64Val (c : UInt8) : Nat` | UInt8, Nat | none (if-chain) | no | no | none | `UInt8.toNat` | nothing beyond inlining (comparisons, sub, add) |
| 17 | `Image.base64Decode` | Image.lean:104 | 31 | `def base64Decode (bs0 : ByteArray) : Option ByteArray := Id.run do` | Nat, UInt32, UInt8, ByteArray, Option | `Id.run do`, one `for g in [0:full]`, early `return none` | `emptyWithCapacity` + `push` | no | `% 4` ×6, `/ 4`, `4 * g`, `full * 3` | `dropBytes` (Image.lean:59, allocates filtered copy), `isAsciiWs`, `at'`, `b64Val` | Option result (needs status flag); output allocation; pre-pass `dropBytes` allocates; `%4`,`/4`,`*4` are shift/mask-expressible, `full*3` is not (add-expressible) |
| 18 | `Font.b64Digit` | LeanSvg/Font.lean:554 | 7 | `@[inline] def b64Digit (c : UInt8) : UInt32` | UInt8, UInt32 | none | no | no | none | `UInt8.toUInt32` | nothing beyond inlining; UInt32 wrap on `-` (branches guard it) |
| 19 | `Font.strByte` | Font.lean:1068 | 2 | `@[inline] def strByte (s : String) (i : Nat) : UInt8` | String, `String.Pos.Raw`, UInt8, Nat | none | no | no | none | `String.rawEndPos`, `String.getUTF8Byte` | String as read-only byte array (needs String→bytes model) |
| 20 | `Font.base64DecodeInto` | Font.lean:1076 | 15 | `def base64DecodeInto (out : ByteArray) (s : String) : ByteArray := Id.run do` | String, UInt32, UInt8, ByteArray, Nat | `Id.run do`, `for q in [0:n/4]`, 3 × `break` | `push` on threaded `out` | no | `/ 4`, `4 * q` | `b64Digit`, `strByte`, `String.utf8ByteSize` | String input; output append; otherwise shifts/masks/compare only |
| 21 | `Font.base64Decode` / `base64DecodeChunks` | Font.lean:1093 / :1098 | 2 / 6 | `def base64Decode (s : String) : ByteArray`; `def base64DecodeChunks (chunks : Array String) : ByteArray := Id.run do` | String, Array String, ByteArray, Nat | none / `for c in chunks` + `Array.foldl` closure | allocates, threads `out` | no | `/ 4 * 3` | `base64DecodeInto`, `Array.foldl` | Array of String; allocation |
| 22 | `Font.base64Range` | Font.lean:572 | 14 | `def base64Range (chunks : Array String) (per start len : Nat) : ByteArray := Id.run do` | Array String, UInt32, Nat, ByteArray | `for k in [0:len]` | `push` | no | `n / per`, `n % per`, `j / 3`, `j % 3`, `4 * …` | `b64At` (Font.lean:563), `Array.getD` | general `/`, `%` by variable and by 3; Array of String |
| 23 | `FontFace.base64` | LeanSvg/FontFace.lean:118 | 19 | `def base64 (s : ByteArray) : Option ByteArray := Id.run do` | Nat (`acc`, `n`), UInt32, UInt8, ByteArray, Option | `for c in s` (iterates bytes), `continue`, `break`, early `return none` | `push` | no | `acc * 64`, `/ 65536 % 256`, `/ 256 % 256`, `% 256`, `/ 16`, `/ 1024`, `/ 4` (all powers of two) | `isWs`, `Font.b64Digit` | Option; output allocation; all mul/div/mod are by powers of two |
| 24 | `Svg.hexVal` (identical bodies: `FontFace.hexVal` FontFace.lean:138, `Image.hexDigit` Image.lean:66) | LeanSvg/Svg.lean:690 | 5 | `def hexVal (c : UInt8) : Option Nat` | UInt8, Nat, Option | none | no | no | none | `isDigit`, `UInt8.toNat` | Option result (sentinel needed) |
| 25 | `Svg.parseHexColor` | Svg.lean:696 | 15 | `def parseHexColor (bs : ByteArray) : Option Rgba := Id.run do` | Nat, Array Nat, ByteArray, Option, structure `Rgba` (4 Nat fields, Canvas.lean:16) | `for k in [1:bs.size]`, early return | `Array.push` (temp `ds`) | no | `* 17`, `* 16` | `hexVal`, `at'`, `Array.getD`, local closure `g` | temp Array allocation (≤ 8 entries); structure result; `*17` |
| 26 | `Bidi.hexDigit` / `Bidi.decodeHex` | LeanSvg/Bidi.lean:277 / :285 | 4 / 15 | `def hexDigit (c : Char) : Nat`; `def decodeHex (s : String) (widths : Array Nat) : Array Nat := Id.run do` | Char, String, List Char→Array Char (`s.toList.toArray`), Array Nat | 3 nested `for` (2 range, 1 over Array), `Array.foldl` | `Array.push` | no (decodes generated tables) | `v * 16`, `cs.size / rec_`, `n * widths.size` | `String.toList`, `List.toArray`, `Array.foldl`, `Array.getD`, `Array.mkEmpty` | Char/String/List; Array Nat output (8-byte stores); variable `/` and `*` |
| 27 | `Text.decodeUtf8` | LeanSvg/Text.lean:307 | 25 | `def decodeUtf8 (bs : ByteArray) : Array Nat := Id.run do` | Nat, ByteArray, Array Nat | `for _ in [0:bs.size]` used as fuel with `let mut i`, `break`; two local closures `cont`, `isCont` | `Array.push` (output of code points) | no | `* 0x40`, `* 0x1000`, `* 0x40000` (powers of two) | `at'`, `UInt8.toNat`, `Array.emptyWithCapacity` | **output is `Array Nat`** (word-sized elements: needs 8-byte/4-byte stores; allocation); local closures (inline) |
| 28 | `StixNonUnicode.utf8` (encoder, 3/4-byte forms only) | LeanSvg/StixNonUnicode.lean:27 | 6 | `def utf8 (cp : Nat) : Array UInt8` | Nat, UInt8, Array UInt8 | none | array literal `#[…]` | no | `/ 0x1000`, `/ 0x40 % 0x40`, `/ 0x40000`, `% 0x40` (powers of two) | `Nat.toUInt8` | allocation of 3–4-element result; else shifts/masks |
| 29 | `ShapeText.utf8Len` | LeanSvg/ShapeText.lean:63 | 1 | `def utf8Len (cp : Nat) : Nat` | Nat | none | no | no | none | none | nothing |
| 30 | `Use.fmtFixed` (integer→decimal printer: `v / 2^bits` as exact decimal) | LeanSvg/Use.lean:151 | 5 | `def fmtFixed (v : Int) (bits : Nat) : String` | Int, Nat (unbounded: `5 ^ bits`), String, Char, List Char | none | builds String via `++` | no | `% 2^bits`, `* 5^bits`, `/ 2^bits`, `^` | `Int.natAbs`, `toString` on Nat (= `Nat.repr`, core), `String.length`, `String.ofList`, `List.replicate` | **no in-repo digit loop**: decimal conversion is core `Nat.repr`/`Nat.toDigits`; needs `/ 10`, `% 10`, String output, exponentiation, signed Int |
| 31 | `Image.percentDecode` | LeanSvg/Image.lean:74 | 17 | `def percentDecode (bs : ByteArray) : ByteArray := Id.run do` | Nat, UInt8, ByteArray, Option | `for i in [0:bs.size]`, `let mut skip`, `continue`, early `return bs` | `emptyWithCapacity` + `push` | no | `hi * 16` | `findByte`, `at'`, `hexDigit` | output allocation; Option from `hexDigit`; call to `findByte` |
| 32 | `FontFace.percentDecode` | LeanSvg/FontFace.lean:145 | 14 | `def percentDecode (s : ByteArray) : ByteArray := Id.run do` | Nat, UInt8, ByteArray, Option | `for _ in [0:s.size]` as fuel, `let mut i`, `break`; 3-way tuple `match` | `push` | no | `h * 16` | `at'`, `hexVal` | same as 31 |
| 33 | `PngDecode.be32` (u32 BE reader) | LeanSvg/PngDecode.lean:36 | 3 | `@[inline] def be32 (b : ByteArray) (i : Nat) : Nat` | Nat, ByteArray | none | no | no | none (`<<< \|\|\|`) | `at'`, `UInt8.toNat` | nothing beyond inlining `at'` (4 byte loads, shl, or) |
| 34 | `GifDecode.le16`; `Font.u8/u16/u32` (Font.lean:119-121); `Font.i8/i16` (:123-:129); `JpegDecode.u16` (JpegDecode.lean:41, private) | LeanSvg/GifDecode.lean:42 | 1–3 each | `@[inline] def le16 (b : ByteArray) (i : Nat) : Nat`; `@[inline] def u16 (bs : ByteArray) (i : Nat) : Nat`; `@[inline] def u32 (bs : ByteArray) (i : Nat) : Nat`; `@[inline] def i16 (bs : ByteArray) (i : Nat) : Int` | Nat, Int, ByteArray | none | no | no | `* 256`, `* 65536` (powers of two) | `at'`, each other | `i8/i16` return `Int` (signed); otherwise nothing |
| 35 | `Bytes.at'`, `isWs`, `isDigit`, `isAlpha`, `isNameChar`, `toLower` | LeanSvg/Bytes.lean:15-23 | 1–2 each | `@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8` etc. | UInt8, Nat, Bool, ByteArray | none | no | no | none | — | dependent `if h : i < bs.size then bs[i] else 0` |
| 36 | `Bytes.skipWhile`, `findByte`, `startsWith`, `findSeq`, `eqAscii`, `eqAsciiCI` | Bytes.lean:26, 38, 46, 55, 63, 72 | 5–7 each | e.g. `def findByte (bs : ByteArray) (i : Nat) (c : UInt8) : Nat := Id.run do`; `def skipWhile (bs : ByteArray) (i : Nat) (p : UInt8 → Bool) : Nat := Id.run do` | Nat, UInt8, Bool, ByteArray, String (`s.toUTF8`) | `for _ in [i:bs.size]` + `let mut j`, `break`/early `return` | no | no | none | `at'`; `skipWhile` takes a **function argument** `p`; `startsWith/eqAscii*` take a `String` and call `toUTF8` | first-class predicate `p` (needs specialization); String literal as second read-only byte array |
| 37 | `Bytes.trim`, `lower`, `splitTrim` | Bytes.lean:81, 89, 96 | 6, 5, 10 | `def trim (bs : ByteArray) : ByteArray`; `def lower (bs : ByteArray) : ByteArray`; `def splitTrim (bs : ByteArray) (sep : UInt8) : Array ByteArray` | ByteArray, Array ByteArray | `for` loops | `ByteArray.extract`, `push`, `Array.push` | no | none | `skipWs`, `findByte`, `trim` | allocation (`extract`, new ByteArray, Array of ByteArray) |
| 38 | `Inflate.peek` (LSB-first bit reader) | LeanSvg/Inflate.lean:27 | 5 | `@[inline] def peek (inp : ByteArray) (bp n : Nat) : Nat` | Nat, ByteArray | none | no | no | `bp / 8`, `bp % 8`, `% (1 <<< n)` (powers of two) | `at'` | nothing (shift/mask-expressible) |
| 39 | `Fixed.parseDecimal` (decimal *parser*, not printer) | LeanSvg/Fixed.lean:78 | ~60 | `def parseDecimal (bs : ByteArray) (i : Nat) : Option (Bool × Nat × Int × Nat) := Id.run do` | Nat, Int, Bool, Option, 4-tuple | `Id.run do`, `for` loops | no | no | `* 10` | `at'`, `isDigit` | Option of 4-tuple; signed `Int` exponent; `* 10` |

Not present in the closure: an Adler-32 over a plain byte range (only the row-structured `adler32Rows`); a standalone integer→decimal digit loop (all decimal printing goes through core `toString`/`s!"…"` interpolation: `Use.fmtFixed`, error messages at Render.lean:971-972, 1074, 1088-1089, Use.lean:275, Filter.lean:939).
CRC-32 is also used on the decode side: `PngDecode` calls `Png.crc32Range` (PngDecode.lean:87, :119). Adler-32 is not checked on decode (PngDecode.lean:18-19, Inflate.lean:13).

### Verbatim source of the 4 smallest

CRC-32, byte-at-a-time core, with its table (LeanSvg/Png.lean:28-32, 52-54):

```lean
def crcTable : Array UInt32 :=
  Array.ofFn (n := 256) fun i =>
    (List.range 8).foldl
      (fun (c : UInt32) _ => if c &&& 1 == 1 then (0xEDB88320 : UInt32) ^^^ (c >>> 1) else c >>> 1)
      i.val.toUInt32
```
```lean
def crcBytes (bs : ByteArray) (start stop : Nat) (c : UInt32) : UInt32 :=
  bs.foldl (fun c b => crcTable.getD ((c ^^^ b.toUInt32) &&& 0xFF).toNat 0 ^^^ (c >>> 8))
    c start stop
```

CRC-32 driver (LeanSvg/Png.lean:88-95; `crcRun4` at :66-84 is the 4-bytes-per-step loop it calls):

```lean
def crc32Range (bs : ByteArray) (start stop : Nat) : Nat :=
  let hi := Nat.min stop bs.size
  let lo := Nat.min start hi
  let quads := (hi - lo) / 4
  let c := crcRun4 bs lo quads 0xFFFFFFFF
  (crcBytes bs (lo + quads * 4) hi c ^^^ 0xFFFFFFFF).toNat

def crc32 (bs : ByteArray) : Nat := crc32Range bs 0 bs.size
```

Adler-32 inner loop (LeanSvg/Png.lean:113-118) and driver (:137-152):

```lean
def adlerChunk (rgba : ByteArray) (i fuel : Nat) (a b : UInt64) : UInt64 × UInt64 :=
  match fuel with
  | 0 => (a, b)
  | fuel' + 1 =>
    let a' := a + (if _ : i < rgba.size then rgba[i].toUInt64 else 0)
    adlerChunk rgba (i + 1) fuel' a' (b + a')
```
```lean
def adler32Rows (rgba : ByteArray) (rowBytes h : Nat) : Nat := Id.run do
  let mut a : Nat := 1
  let mut b : Nat := 0
  let nchunks := (rowBytes + 5551) / 5552
  for y in [0:h] do
    b := (b + a) % 65521
    let base := y * rowBytes
    for c in [0:nchunks] do
      let lo := base + c * 5552
      let hi := Nat.min (base + rowBytes) (lo + 5552)
      let quads := (hi - lo) / 4
      let q := adlerChunk4 rgba lo quads a.toUInt64 b.toUInt64
      let r := adlerChunk rgba (lo + quads * 4) (hi - lo - quads * 4) q.1 q.2
      a := r.1.toNat % 65521
      b := r.2.toNat % 65521
  return (b <<< 16) ||| a
```

Big-endian u32 writer and reader (LeanSvg/Png.lean:154-156; LeanSvg/PngDecode.lean:36-38):

```lean
def be32 (n : Nat) : ByteArray :=
  (((ByteArray.empty.push ((n >>> 24) &&& 0xFF).toUInt8).push ((n >>> 16) &&& 0xFF).toUInt8).push
    ((n >>> 8) &&& 0xFF).toUInt8).push (n &&& 0xFF).toUInt8
```
```lean
@[inline] def be32 (b : ByteArray) (i : Nat) : Nat :=
  ((at' b i).toNat <<< 24) ||| ((at' b (i + 1)).toNat <<< 16) |||
    ((at' b (i + 2)).toNat <<< 8) ||| (at' b (i + 3)).toNat
```

Hex digit and base64 digit (LeanSvg/Svg.lean:690-694; LeanSvg/Font.lean:554-560; helper LeanSvg/Bytes.lean:15-16):

```lean
def hexVal (c : UInt8) : Option Nat :=
  if isDigit c then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none
```
```lean
@[inline] def b64Digit (c : UInt8) : UInt32 :=
  if 65 ≤ c && c ≤ 90 then c.toUInt32 - 65
  else if 97 ≤ c && c ≤ 122 then c.toUInt32 - 71
  else if 48 ≤ c && c ≤ 57 then c.toUInt32 + 4
  else if c == 43 then 62
  else if c == 47 then 63
  else 64
```
```lean
@[inline] def at' (bs : ByteArray) (i : Nat) : UInt8 :=
  if h : i < bs.size then bs[i] else 0
```

---

## B. Feature tabulation over the import closure of `LeanSvg/Render.lean`

Scope: 101 files, 33,067 lines (raw, incl. comments/doc strings). 35 of the files are `LeanSvg/Fonts/*.lean` (generated; 2,649 lines but ~32 MB, base64 string literals; 175 defs). The repo's `LeanSvg/` has 36 files under `Fonts/` (one is a README), plus `Cli.lean` (not in closure).

Declarations (column-0 commands after comment stripping): `def` 1658 (no `partial def`, no `private def` at column 0 except those matched with modifiers — modifiers are included in the 1658), `abbrev` 7, `instance` 1, `example` 8, `structure` 123, `inductive` 52, `class` 0, `theorem` 0, `namespace` 168, `open` 52, `set_option` 2, `deriving instance` 1. Local definitions: `let rec` 0; `where` blocks 2 (ShapeRun.lean:428, Shader.lean:989).
Def body sizes (def+abbrev+instance = 1666): ≤5 lines 632; 6–20 lines 711; 21–60 lines 249; >60 lines 74. Largest: `Svg.interpretWith` 1110 lines (Svg.lean:3937), `Text.layout` 737 (Text.lean:765), `Render.renderNodes` 387 (Render.lean:580), `Svg.textShapes` 265 (Svg.lean:3251), `Svg.applyProp` 257 (Svg.lean:2199), `Raster.rasterize` 192 (Raster.lean:149), `Brotli.decompress` 165 (Brotli.lean:386), `Raster.rasterizeCrisp` 160 (Raster.lean:371), `PatternRender.build` 152 (PatternRender.lean:244).

| Feature | Count (defs of 1666 unless stated) | Heuristic |
|---|---|---|
| `partial` | 0 | word `partial` anywhere in stripped text |
| `termination_by` / `decreasing_by` | 0 | word grep |
| Explicit self-recursion | 26 defs (28 regex hits; 2 false positives: `F32.sqrt` Canvas.lean:501 calls `Nat.sqrt`; the `Repr` instance) | def's own name occurs in its body. All 26 are structural on a `Nat` fuel/depth argument (`| 0 … | fuel+1` or `match fuel with`). List: Png.lean:66,113,122,184,197; Inflate.lean:119,145,193; Gzip.lean:22; PngDecode.lean:78,110; GifDecode.lean:48,62,95; Font.lean:769; Shape.lean:1445; ShapeRun.lean:285,555,1073; Use.lean:224; Clip.lean:277,302; Marker.lean:386; PatternRender.lean:244; Render.lean:580; Filter/ConvolveMatrix.lean:54 (not checked individually whether each is tail-recursive) |
| Defs mentioning `fuel` | 25 | word grep |
| `Id.run` | 340 defs (367 occurrences of `.run`) | `\bId\.run\b` |
| `do` blocks | 398 | `\bdo\b` |
| `for … in` | 354 defs; 295 over a range `[a:b]`, 113 over a collection (overlap) | `for … in [` vs. `for … in <non-[>`; `[0:` occurs 449 times |
| `while` | 2 defs, 4 occurrences: Svg.lean:4303, 4326, 4769 (inside `interpretWith`), Marker.lean:161 (`getSubpathStart`) | word grep. Note: Render.lean's header (line 17) says "no `partial`"; in Lean core, `while` elaborates to `Loop.forIn`, whose core implementation is a `partial def` (statement about Lean core from general knowledge, not checked against the v4.34.0 sources here). No `repeat`. |
| `let mut` | 334 | `let\s+mut` |
| `break` / `continue` | 137 | word grep |
| `return` (incl. early return) | 383 | word grep |
| lambdas (`fun`, `·`) | 281 | `\bfun\b`, `(·`, `·)` |
| Higher-order calls | 202 defs. Occurrence counts: `.map` 244, `.bind` 98, `.foldl` 48, `.contains` 45, `.modify` 39, `.filter` 35, `.any` 35, `.find?` 34, `.all` 15 | `.name` grep for map/foldl/filter/any/all/find?/bind/… (receiver type not resolved: `.map`/`.bind` include `Option`) |
| Function-typed parameters | present, e.g. `Bytes.skipWhile (p : UInt8 → Bool)` Bytes.lean:26, `Image.dropBytes`/`trimBy` Image.lean:59/142 | not counted systematically |
| `Nat` | 910 defs | `\bNat\b`. Unbounded by type; no `Fin`-bounded scalars except `Array.ofFn` indices |
| `Int` | 331 defs + 179 mentioning `Fx` (`abbrev Fx := Int`, Fixed.lean:17) | word grep. Docs state values are clamped to ±2^30 (Fixed.lean:23-28) but the type is arbitrary precision |
| `Float` | **0** uses of Lean `Float`/`Float32` in the closure, and 0 in any `.lean` file of the repo (one comment hit, Oklab.lean:13 "Float-free") | `\bFloat` over all files. Render's output therefore does not depend on hardware floats. There is a **software float**: `abbrev F32 := Nat` (Canvas.lean:343) with `mant/expo/norm/add/mul/div/sqrt/lt…` (Canvas.lean:345-560) implemented on `Nat` with shifts, `*`, `/`, `Nat.sqrt`; used in 13 files (Canvas, Mask, Marker, FilterApply, Filter, Filter/{Turbulence,ConvolveMatrix,Morphology,Gamma,Lighting}, Render, Font, PatternRender), e.g. `Render.opacityF32` Render.lean:461, `Canvas.compositeBlend` Canvas.lean:793 — output pixels do depend on it |
| `UInt8` | 59 defs (`.toUInt8` 56 occurrences) | type name or `toUInt8` |
| `UInt16` / `USize` / `BitVec` | 0 / 0 / 0 | word grep |
| `UInt32` | 13 defs (`.toUInt32` 18) | — |
| `UInt64` | 4 defs (all Png.lean Adler) | — |
| `Array` | 521 defs; `Array <scalar>` (Nat/Int/Fx/UInt8/UInt32/Bool) in 185; Array of structure/tuple/nested Array in ~150 (rough regex) | `\bArray\b` or `#[`; `#[` occurs 1011 times |
| Array `push` | 189 defs (670 occurrences, incl. ByteArray.push) | `.push` |
| Array `set` family | 103 defs (`.setIfInBounds` 244, `.modify` 39) | `.set!`/`.setIfInBounds`/`.modify`/`.swap`. No `]!` indexing (0), `[i]?` 3 |
| Array read | `.getD` 1250 occurrences, `.size` 1001, `.back?` 90, `.pop` 65 | occurrence counts |
| `ByteArray` | 388 defs (`.extract` 167, `ByteArray.empty` 58, `emptyWithCapacity` 25+) | word grep |
| `String` | 379 defs (includes any def containing a string literal); `s!"…"` interpolation 33 occurrences; `.toUTF8` 29 | `\bString\b` or literal |
| `Char` | 9 defs: Xml.lean:68,137,173; Bidi.lean:277,285; ShapeRun.lean:64; Use.lean:151; JpegDecode.lean:529; Warn.lean:36 | `\bChar\b` or char literal |
| `Substring` | 0 by name (`.drop … .toString` appears at ForeignObject.lean:427, Units.lean:117) | word grep |
| `List` | 37 defs (`List.range` 35 occurrences, `.toList`) | word grep |
| `Option` | 496 defs (`.isSome` 80, `.isNone` 23, `.bind` 98) | `Option`/`some`/`none` |
| `Except` / `throw` / `try` | `Except` in 23 defs; `throw` in 15 defs; `try` 0; `.ok`/`.error` 27/18 occurrences | word grep |
| `match` | 359 defs with `match`; 27 more with equation-style `\|` arms | word grep |
| Dependent `if h : …` | 9 defs; `by …` proof terms in 4 defs (all `by omega` index proofs in Png.lean / Font.lean) | regex |
| `structure` | 123 declarations. Field count (lines `name :` in body): median 5, mean 6.7; 55 have <5, 50 have 5–9, 10 have 10–14, 5 have 15–19, 3 have ≥20. Largest: `Svg.Style` 77 (Svg.lean:75), `Font` 29 (Font.lean:42), `Text.SpanProps` 28 (Text.lean:191), `Render.Layer` 19 (Render.lean:477), `Shape.St` 18 (Shape.lean:474) | — |
| `inductive` | 52; recursive: 2 (`ShapeRun.Re` ShapeRun.lean:540, 5 ctors; `Svg.Paint` Svg.lean:39, 4 ctors). Largest: `Filter.Kind` 16 ctors (Filter.lean:193), `Baseline.AlignmentBaseline` 12 | recursive = own name in a constructor type. The document tree is flat: `Array Xml.Event` / `Array Svg.Node` (`Svg.Node` 3 ctors, non-recursive, Svg.lean:492) |
| `HashMap`/`HashSet`/`RBMap` | `Std.HashMap` only: 20 lines, 10 defs, key types `String` and `Clip.Key`: Use.lean:315; Filter/Image.lean:170; Filter.lean:298,331; Svg.lean:3065,3079-3088,3254,4978-4979,5010-5011; Clip.lean:265 (`abbrev Cache := Std.HashMap Key Res`); Marker.lean:360-361,386 | word grep |
| Type classes / instances | `class` 0; hand-written `instance` 1 (`Repr Face`, FontFace.lean:53); `deriving` clauses 148 lines: Inhabited 143, Repr 62, BEq 35, DecidableEq 4, Hashable 1; `deriving instance Repr for ByteArray` (Css.lean:42) | grep |
| Monads other than `Id`/`Except`/`Option` | 1: `abbrev M := StateM St` (Shape.lean:497), used by the shaping code in Shape.lean / ShapeRun.lean (e.g. ShapeRun.lean:745). No `StateT`/`ExceptT`/`ReaderT` | word grep. `←` occurs 205 times |
| `IO` | 0 in closure (IO is in `Main.lean`, `LeanSvg/Cli.lean`, the dump tools — outside the closure) | `\bIO\b` |
| `Task` | 1 def: `Render.renderBands` (Render.lean:1028-1047) uses `Task.spawn`/`.get`; only reached when `opts.threads ≥ 2` (`bandCount`, Render.lean:1008) | word grep |
| Mutual recursion | 0 `mutual` blocks | grep |
| `unsafe` / `@[extern]` / `@[implemented_by]` | 0 / 0 / 0 | grep |
| `sorry` / `axiom` / `panic!` / `get!` / `]!` | 0 | grep |
| `Thunk` / laziness | `Thunk` in 2 defs: `Lighting.lnTab`, `expTab` (Filter/Lighting.lean:277, 279). Font loading uses `Unit →` thunks: `e.font ()` (ShapeText.lean:57) | grep |
| Universe polymorphism / generic defs | `universe` 0; defs with a type parameter: 3 (`Shader.pickCommon` Shader.lean:479, `Pattern.pickCommon` Pattern.lean:165, `Bidi.backScan` Bidi.lean:484) | Greek letter / `: Type` in signature |
| Tuples (`×`) | 289 defs | grep |
| Multiplication | 454 defs contain `*` (1968 ` * ` occurrences) | grep |
| Division | ` / ` in 157 defs (277 occ.); `Int.ediv/tdiv/fdiv` in 138 defs (`Int.ediv` 412 occ., `tdiv` 9, `fdiv` 4) | grep |
| Modulo | ` % ` in 82 defs (134 occ.); `Int.emod/tmod` in 20 defs (30 / 5 occ.) | grep |
| Bit ops | 176 defs; occurrences: `&&&` 238, `>>>` 225, `<<<` 98, `\|\|\|` 80, `^^^` 17 | grep |
| Other numeric | `Nat.sqrt` 26, `Nat.log2` 5, `^` (e.g. `2 ^ 35`, `10 ^ n`, `5 ^ bits`) | grep |

---

## C. Top-level shape of `render`

`render` (Render.lean:1099-1100) = `(·.1) <$> renderWithWarnings opts input`. `renderWithWarnings` (Render.lean:1072-1095), in order:

1. `input.size > maxInput` (64 MiB) → `throw` (:1074)
2. `Xml.parse input : Except String (Array Xml.Event)` (:1075)
3. `Svg.interpretWith { outSize := Render.outSize events opts } events : Except String Svg.Doc` (:1076) — `outSize` (:1056) calls `Svg.parseRoot` + `canvasSetup`
4. `Marker.expand doc` (:1082)
5. `RootFit.apply doc` (:1085)
6. `Render.canvasSetup doc.root opts` → `(w, h, _, _)`; checks against `maxDim` 16384 / `maxPixels` 2^24 (:1086-1089)
7. `Render.bandCount opts.threads h` (:1090); then `Render.renderRgba opts doc` (serial, :967-977) or `Render.renderBands` (`Task.spawn` per band, :1028). `renderRgba` = `canvasSetup` ×2 → `renderNodes` (:580, fuel-recursive, 387 lines; calls `drawShape` :243, clip/mask/filter/pattern code) on `Canvas.new w h bg` → `cv.toRgbaBytes` (Canvas.lean:279)
8. `Png.encode w h rgba` (:1095; Png.lean:224)

Lines per stage (whole files in the closure, raw lines incl. comments; "defs" = def+abbrev+instance):

| Stage | files | lines | defs |
|---|---|---|---|
| shared: Bytes, Fixed, Geom | 3 | 1418 | 105 |
| 1 XML parse (Xml) | 1 | 344 | 14 |
| 2a CSS (Css) | 1 | 575 | 24 |
| 2b `<use>` / foreignObject rewriting (Use, ForeignObject) | 2 | 833 | 37 |
| 2c SVG interpret: Svg, Units, Viewport, BasicShape, Oklab, Warn, Pattern, StixNonUnicode(+Table) | 9 | 6528 | 218 |
| 2d text layout, shaping, bidi: Text, TextPath, Baseline, Synth, VertOrient, FamilyMatch, FontSet, ShapeText, ShapeRun, Shape, ShapeData, Bidi | 12 | 6406 | 349 |
| 2e font parsing: Font, FontFace, Woff, Brotli, BrotliData | 5 | 2676 | 144 |
| 2f embedded font data (Fonts/*, generated base64) | 35 | 2649 | 175 |
| 2g image decoders: Image, ImageData, SvgImage, PngDecode, JpegDecode, Jpeg/Huffman, Jpeg/Idct, GifDecode, Inflate, Gzip | 10 | 2374 | 136 |
| 3 marker expansion + root fit (Marker, RootFit) | 2 | 579 | 28 |
| 4a render driver (Render) | 1 | 1102 | 29 |
| 4b rasterizer, canvas/compositing, shaders: Raster, Canvas, Shader, DashSeg | 4 | 2719 | 133 |
| 4c clip / mask / pattern: Clip, Mask, PatternRender | 3 | 975 | 46 |
| 4d filters: Filter, FilterApply, FilterFrame, Filter/* (9) | 12 | 3649 | 207 |
| 5 PNG encode (Png) | 1 | 240 | 21 |
| total | 101 | 33067 | 1666 |

Stages 2d–2g are reached from stage 2c (`Svg.lean` imports Text, FontFace, Image, SvgImage, Css, Use, ForeignObject, Filter, Shader, Pattern, …). The import graph is not a strict pipeline: e.g. `PngDecode` imports `Png` (for CRC), `Brotli` imports `Font` (for base64), `Svg` imports `Canvas`/`Shader`/`Filter`.

10 largest files (all in the closure; also the 10 largest in the repo):

| lines | file |
|---|---|
| 5050 | LeanSvg/Svg.lean |
| 1540 | LeanSvg/Shape.lean |
| 1503 | LeanSvg/Text.lean |
| 1250 | LeanSvg/ShapeRun.lean |
| 1154 | LeanSvg/Font.lean |
| 1144 | LeanSvg/Filter.lean |
| 1102 | LeanSvg/Render.lean |
| 1071 | LeanSvg/Shader.lean |
| 1043 | LeanSvg/Geom.lean |
| 847 | LeanSvg/Bidi.lean |

(Repo total: 35,306 lines of `.lean` outside `.lake`, including `spec/`, `tests/`, `docs/`, and tool mains.)

---

## D. Core/Std functions used most

Occurrence counts over the 101 files after comment/string stripping. `.name` counts do not resolve the receiver type (noted where ambiguous); project-defined names (`.x`, `.lineTo`, `Fx.mul`, …) were removed by hand.

| # | Function | count | note |
|---|---|---|---|
| 1 | `Array.getD` | 1250 | `.getD`; includes some `Option.getD` / `HashMap.getD` |
| 2 | `Array.size` / `ByteArray.size` | 1001 | `.size` |
| 3 | `Array.push` / `ByteArray.push` | 670 | `.push` |
| 4 | `Int.ediv` | 412 | qualified |
| 5 | `Id.run` | 359 | |
| 6 | `UInt8.toNat` / `UInt32.toNat` / `Int.toNat` | 326 | `.toNat` (`Int.toNat` qualified: 21) |
| 7 | `Array.map` / `Option.map` | 244 | `.map` |
| 8 | `Array.setIfInBounds` | 244 | |
| 9 | `ByteArray.extract` (also `Array.extract`) | 167 | |
| 10 | `Nat.min` | 128 | qualified (`.min` total 147) |
| 11 | `Option.bind` | 98 | `.bind` |
| 12 | `Array.back?` | 90 | |
| 13 | `Option.isSome` | 80 | |
| 14 | `Array.emptyWithCapacity` / `ByteArray.emptyWithCapacity` | 72 | 47 / 25 qualified |
| 15 | `Array.isEmpty` / `String.isEmpty` / `ByteArray.isEmpty` | 70 | |
| 16 | `Array.replicate` | 68 | |
| 17 | `Int.natAbs` | 69 | |
| 18 | `Array.pop` | 65 | |
| 19 | `ByteArray.empty` | 58 | |
| 20 | `Nat.toUInt8` / `UInt32.toUInt8` | 56 | |
| 21 | `Array.range` / `List.range` | 49 | 14 / 35 qualified |
| 22 | `Array.foldl` (+ `List.foldl`, `ByteArray.foldl`) | 48 | |
| 23 | `Array.contains` / `HashMap.contains` | 45 | |
| 24 | `Nat.max` | 41 | qualified |
| 25 | `Array.modify` | 39 | |
| 26 | `Array.filter` | 35 | |
| 27 | `Array.any` | 35 | |
| 28 | `Array.find?` | 34 | |
| 29 | `Int.emod` | 30 | |
| 30 | `String.toUTF8` | 29 | |
| 31 | `Nat.sqrt` | 26 | |
| 32 | `Int.ofNat` | 24 | |
| 33 | `Option.isNone` | 23 | |
| 34 | `Std.HashMap` (`insert` 16, `getD`/`get?`/`contains`) | 20 type mentions | |
| 35 | `Nat.toUInt32` / `UInt8.toUInt32` | 18 | |
| 36 | `Array.all` | 15 | |
| 37 | `List.toArray` | 17 | `.toArray` |
| 38 | `Int.tdiv` / `Int.fdiv` / `Int.tmod` | 9 / 4 / 5 | |
| 39 | `Nat.log2` | 5 | |

Operators (not functions) with the same need for counterparts: `*` 1968, `[a:b]` range loops 449, `/` 277, `&&&` 238, `>>>` 225, `←` 205, `++` 137 (ByteArray/Array/String append), `%` 134, `<<<` 98, `|||` 80, `^^^` 17.
Low-count but distinct core dependencies: `toString` on `Nat` / `s!` interpolation (33), `String.fromUTF8?` (1, Bytes.lean:108), `Char.ofNat` (3, Xml.lean:154, 194), `String.ofList` (4), `String.getUTF8Byte`/`rawEndPos` (Font.lean:564, 1069), `ByteArray.copySlice` (Png.lean:192), `ByteArray.foldl` (Png.lean:53), `Array.ofFn` (3), `Task.spawn` (1), `Thunk.mk` (2), `Nat.pow` (`^`).
